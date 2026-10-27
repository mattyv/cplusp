#include "CplusPChecks.h"

namespace cplusp::detail {

namespace {
// The patterns of the policy run on the full tree. clang-tidy 18 gives a check no traversal kind
// unless it overrides getCheckTraversalKind, so a pattern sees implicit nodes. The `sign_compare`
// pattern relies on that: it matches the cast the compiler adds. Of the hand-written checks below, only three read the
// tree as spelled in the source: mutable, inexact-literal and lambda-limits, through SpelledCheck. The others see the full tree.
class MatcherCheck : public ClangTidyCheck {
public:
  // The base class keeps the context private, so the check keeps its own pointer.
  MatcherCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}

  void registerMatchers(MatchFinder *Finder) override {
    // Every option of this check is a pattern. The options of other checks do not start with this prefix.
    const std::string Prefix = (getID() + ".").str();
    for (const auto &Option : Ctx->getOptions().CheckOptions) {
      StringRef Key = Option.getKey();
      if (!Key.consume_front(Prefix))
        continue;
      // The key is `{rule_id}/{n}`. A rule id has no `/`, so the last one ends the id.
      StringRef Rule = Key.rsplit('/').first;
      Rules.insert(Rule);
      if (auto Why = addPattern(Finder, Rule, Option.getValue().Value))
        configurationDiag("rule %0 has an invalid matcher: %1") << Rule << *Why;
    }
  }

  void check(const MatchFinder::MatchResult &Result) override {
    // Each pattern is bound to its rule id, so the bound nodes of one match name the rule.
    // A pattern may bind other nodes under its own names. Those are not findings.
    for (const auto &Bound : Result.Nodes.getMap()) {
      if (!Rules.contains(Bound.first))
        continue;
      SourceLocation Loc = Bound.second.getSourceRange().getBegin();
      if (Loc.isInvalid())
        continue;
      // A node from a macro is reported where the macro is used. clang-tidy drops a finding
      // inside a macro of a system header, and `setjmp` is such a macro.
      diag(Result.SourceManager->getFileLoc(Loc), "%0") << Bound.first;
    }
  }

private:
  ClangTidyContext *Ctx;
  // The rule ids read from the options.
  llvm::StringSet<> Rules;

  // Compile one pattern and add it to the finder. Returns the reason when it cannot.
  std::optional<std::string> addPattern(MatchFinder *Finder, StringRef Rule, StringRef Pattern) {
    dynamic::Diagnostics Error;
    StringRef Code = Pattern;
    std::optional<internal::DynTypedMatcher> Parsed = dynamic::Parser::parseMatcherExpression(Code, &Error);
    if (!Parsed)
      return Error.toStringFull();
    std::optional<internal::DynTypedMatcher> Bound = Parsed->tryBind(Rule);
    if (!Bound)
      return "it is not a node matcher, so it has nothing to bind. Start it with a matcher such as varDecl.";
    if (!Finder->addDynamicMatcher(*Bound, this))
      return "it is not a matcher for a declaration, statement, type or similar node.";
    return std::nullopt;
  }
};

// ------------------------------------------------------------ hand-written checks

// These checks read what the author wrote. The traversal skips implicit nodes, such as the begin and end calls
// of a range-for, and template instantiations. A matcher also looks through implicit casts and temporaries.
class SpelledCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  std::optional<TraversalKind> getCheckTraversalKind() const override { return TK_IgnoreUnlessSpelledInSource; }
};

AST_MATCHER(FieldDecl, isMutableField) { return Node.isMutable(); }

} // namespace

// The declaration is in namespace std, however deep. A member of a std class counts, and so does std::ranges.
bool inStdNamespace(const Decl *Declaration) {
  for (const DeclContext *Context = Declaration->getDeclContext(); Context; Context = Context->getParent())
    if (Context->isStdNamespace())
      return true;
  return false;
}

namespace {

AST_MATCHER(Decl, isInStd) { return inStdNamespace(&Node); }

// A call of a std function, or a construction of a std class. An operator other than () is no call here:
// `v.rbegin() + 2` is arithmetic, and the operator is a member of std::reverse_iterator.
auto stdCall() {
  return expr(anyOf(callExpr(callee(functionDecl(isInStd())), unless(cxxOperatorCallExpr(unless(hasOverloadedOperatorName("()"))))),
                    cxxConstructExpr(hasDeclaration(isInStd()))));
}

// cplusp-mutable: every field declared `mutable`.
class MutableCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(fieldDecl(isMutableField()).bind("field"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    diag(Result.Nodes.getNodeAs<FieldDecl>("field")->getLocation(), "field is mutable");
  }
};

// A pure interface has no field, and every function it declares is pure virtual. Its destructor may be declared
// if it is virtual. Its own bases must be pure interfaces too, so the whole class is judged.
// A function template is a function it declares, and it is never pure.
bool isPureInterface(const CXXRecordDecl *Record) {
  Record = Record->getDefinition();
  if (!Record || !Record->field_empty())
    return false;
  for (const Decl *Member : Record->decls()) {
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Member->getAsFunction());
    if (Method && !Method->isImplicit() && !Method->isPureVirtual() && !(isa<CXXDestructorDecl>(Method) && Method->isVirtual()))
      return false;
  }
  // A dependent base has no record yet, so it counts as no base. The check visits every instantiation, decision 0055,
  // where `template <class T> struct X : Concrete, Holder<T>` has its bases.
  return llvm::all_of(Record->bases(), [](const CXXBaseSpecifier &Base) {
    const CXXRecordDecl *Parent = Base.getType()->getAsCXXRecordDecl();
    return !Parent || isPureInterface(Parent);
  });
}

// cplusp-multiple-inheritance: more than one direct base that is not a pure interface. It reads the bases the compiler resolves,
// so it visits template instantiations, decision 0055. An instantiation reports at the place in the pattern.
class MultipleInheritanceCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(cxxRecordDecl(isDefinition(), unless(isImplicit())).bind("class"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Class = Result.Nodes.getNodeAs<CXXRecordDecl>("class");
    if (Class->getNumBases() < 2)
      return;
    auto Heavy = llvm::count_if(Class->bases(), [](const CXXBaseSpecifier &Base) {
      const CXXRecordDecl *Parent = Base.getType()->getAsCXXRecordDecl();
      return Parent && !isPureInterface(Parent);
    });
    if (Heavy > 1)
      diag(Class->getLocation(), "more than one base is not a pure interface");
  }
};

AST_MATCHER(FunctionDecl, isOperatorFunction) { return Node.isOverloadedOperator(); }

const ClassTemplateSpecializationDecl *asSpan(QualType Type) {
  const auto *Span = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Type.getNonReferenceType()->getAsCXXRecordDecl());
  return Span && Span->getName() == "span" && inStdNamespace(Span) ? Span : nullptr;
}

} // namespace

// A type the holder can write through, decision 0055: a non-const lvalue or rvalue reference, a pointer to non-const, or a
// std::span of non-const elements, which writes through like a pointer. An rvalue reference writes too: `f(std::move(a),
// std::move(a))` moves one object twice. A forwarding reference has its instantiated type here, so it counts when it is non-const.
bool isMutableType(QualType Type) {
  Type = Type.getCanonicalType();
  if (const auto *Span = asSpan(Type))
    return !Span->getTemplateArgs()[0].getAsType().isConstQualified();
  return (Type->isReferenceType() || Type->isPointerType()) && !Type->getPointeeType().isConstQualified();
}

namespace {

bool hasMutableParameter(const FunctionDecl *Function) {
  return llvm::any_of(Function->parameters(), [](const ParmVarDecl *Parameter) { return isMutableType(Parameter->getType()); });
}

// A function that may change state: a non-static non-const member, or any function with a parameter it can write through.
// A static member has no object, so only its parameters count.
bool mayChangeState(const FunctionDecl *Function) {
  const auto *Method = dyn_cast<CXXMethodDecl>(Function);
  return (Method && !Method->isStatic() && !Method->isConst()) || hasMutableParameter(Function);
}

bool isAssignmentOrIncrement(OverloadedOperatorKind Operator) {
  switch (Operator) {
  case OO_Equal: case OO_PlusEqual: case OO_MinusEqual: case OO_StarEqual: case OO_SlashEqual: case OO_PercentEqual:
  case OO_AmpEqual: case OO_PipeEqual: case OO_CaretEqual: case OO_LessLessEqual: case OO_GreaterGreaterEqual:
  case OO_PlusPlus: case OO_MinusMinus:
    return true;
  default:
    return false;
  }
}

bool isImpureOperator(const FunctionDecl *Function) {
  return isAssignmentOrIncrement(Function->getOverloadedOperator()) || mayChangeState(Function);
}

// cplusp-impure-operator. An operator that the author defaulted or deleted is exempt, and so is every implicit one.
// It reads parameter types, so it judges each instantiation, decision 0055. An instantiation reports at the place in the pattern.
// The dependent pattern is judged by its spelling only: the kind of operator and the object, not the parameter types, which are
// not known there. So an operator in a template that nothing instantiates still stands, and one that both make is one finding. The call operator of a closure is no operator the author wrote: the check of lambdas judges it.
class ImpureOperatorCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(
        functionDecl(isOperatorFunction(), unless(isImplicit()), unless(isDefaulted()), unless(isDeleted()),
                     unless(cxxMethodDecl(ofClass(cxxRecordDecl(isLambda()))))).bind("operator"),
        this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("operator");
    const auto *Method = dyn_cast<CXXMethodDecl>(Function);
    const bool Impure = Function->isTemplated() ? isAssignmentOrIncrement(Function->getOverloadedOperator()) || (Method && !Method->isStatic() && !Method->isConst())
                                                : isImpureOperator(Function);
    if (Impure)
      diag(Function->getLocation(), "operator is not pure");
  }
};

// ponytail: a name test. The `__wrap_iter` of libc++ passes, and so does a pointer iterator, as in std::array,
// unless a begin call stores it. The upgrade is a list of the library's iterator types, or a test of iterator_category.
AST_MATCHER(ValueDecl, hasIteratorType) {
  const CXXRecordDecl *Record = Node.getType().getNonReferenceType()->getAsCXXRecordDecl();
  return Record && Record->getName().contains("iterator");
}

// cplusp-iterator-arithmetic: (a) begin or end that is not a direct argument of a std call,
// (b) std::next, prev, advance and distance, (c) a variable, parameter or field of an iterator type.
// It reads types the compiler resolves, so it visits template instantiations, decision 0055: `auto it = c.begin()` in a template
// body has an iterator type only in an instantiation, and the finding stands at the place in the pattern. The traversal sees the
// implicit nodes too, so the matchers leave out the begin and end of a range-for and the fields of a closure, and match a call
// by its spelled parents.
class IteratorArithmeticCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    const auto Bounds = anyOf(callee(cxxMethodDecl(hasAnyName("begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend"))),
                              callee(functionDecl(hasAnyName("::std::begin", "::std::end", "::std::cbegin", "::std::cend", "::std::rbegin",
                                                             "::std::rend", "::std::crbegin", "::std::crend"))));
    Finder->addMatcher(callExpr(unless(hasParent(varDecl(isImplicit()))),
                                traverse(TK_IgnoreUnlessSpelledInSource, callExpr(Bounds, unless(hasParent(stdCall())))))
                           .bind("call"),
                       this);
    Finder->addMatcher(callExpr(callee(functionDecl(hasAnyName("::std::next", "::std::prev", "::std::advance", "::std::distance")))).bind("call"), this);
    Finder->addMatcher(valueDecl(anyOf(varDecl(), fieldDecl()), hasIteratorType(), unless(isImplicit())).bind("decl"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call"))
      diag(Call->getBeginLoc(), "iterator function outside a std call");
    else
      diag(Result.Nodes.getNodeAs<ValueDecl>("decl")->getLocation(), "stored iterator");
  }
};

// A capture by reference, or of `this` by pointer. `[*this]` copies the object and passes.
AST_MATCHER(LambdaExpr, capturesByReferenceOrThis) {
  return llvm::any_of(Node.captures(), [](const LambdaCapture &Capture) {
    return Capture.getCaptureKind() == LCK_ByRef || Capture.getCaptureKind() == LCK_This;
  });
}

// A lambda marked `mutable`. Its call changes its own captures, so it carries state between calls.
AST_MATCHER(LambdaExpr, isMutableLambda) { return Node.isMutable(); }

// cplusp-lambda-limits: a lambda that is no direct argument of a std call, that captures by reference or `this`,
// or that is `mutable`.
class LambdaLimitsCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(lambdaExpr(anyOf(unless(hasParent(stdCall())), capturesByReferenceOrThis(), isMutableLambda())).bind("lambda"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    diag(Result.Nodes.getNodeAs<LambdaExpr>("lambda")->getBeginLoc(), "lambda is outside its limits");
  }
};

// ------------------------------------------------------------ roots, decision 0033

// A name for an object: a variable, `this` or the State, then the members under it. The State stands for all that a call
// may reach. `Global` is set when the first step is a global or a static data member that is not const.
const char StateKey = 0, ThisKey = 0;

struct RootPath {
  std::vector<const void *> Steps;
  bool Global = false;
  const Expr *At = nullptr;  // the expression that names the variable, for a path that starts at one
};
using Roots = llvm::SmallVector<RootPath, 2>;

RootPath stateRoot() { return {{&StateKey}, false}; }

// Equal, or one a prefix of the other: the two reach the same storage.
bool related(const RootPath &A, const RootPath &B) {
  const auto Shared = std::min(A.Steps.size(), B.Steps.size());
  return std::equal(A.Steps.begin(), A.Steps.begin() + Shared, B.Steps.begin());
}

bool conflict(const Roots &A, const Roots &B) {
  return llvm::any_of(A, [&](const RootPath &P) { return llvm::any_of(B, [&](const RootPath &Q) { return related(P, Q); }); });
}

// What the walk of an expression found. `ConstHandle` is set when the path passes through the `operator*`, `operator->`, `get`
// or the subscript of an array owner, of a const unique_ptr or shared_ptr.
struct Walk {
  Roots Paths;
  bool ConstHandle = false;
  void add(const Walk &Other) {
    Paths.append(Other.Paths.begin(), Other.Paths.end());
    ConstHandle |= Other.ConstHandle;
  }
};

bool isStdClass(QualType Type, std::initializer_list<StringRef> Names) {
  const CXXRecordDecl *Record = Type.getNonReferenceType()->getAsCXXRecordDecl();
  return Record && Record->getDeclName().isIdentifier() && inStdNamespace(Record) && llvm::is_contained(Names, Record->getName());
}

bool isOwner(QualType Type) { return isStdClass(Type, {"unique_ptr", "shared_ptr"}); }
bool isHandle(QualType Type) { return isStdClass(Type, {"unique_ptr", "shared_ptr", "optional"}); }

// A std function whose result is the object, or part of it. The root of the result is the root of the object, or of the first
// argument of a free function. `move`, `forward` and `as_const` are casts.
bool keepsRoot(const FunctionDecl *Function) {
  return inStdNamespace(Function) && Function->getDeclName().isIdentifier() &&
         llvm::is_contained({"front", "back", "at", "data", "begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend", "get",
                             "subspan", "first", "last", "move", "forward", "as_const"},
                            Function->getName());
}

// `std::as_const` is a cast to const.
bool isAsConst(const FunctionDecl *Function) {
  return Function && inStdNamespace(Function) && Function->getDeclName().isIdentifier() && Function->getName() == "as_const";
}

// The object of a member call, or of an operator that is a member. Null for a free function and a static member.
const Expr *objectOf(const CallExpr *Call) {
  const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getDirectCallee());
  if (!Method || Method->isStatic())
    return nullptr;
  if (const auto *Member = dyn_cast<CXXMemberCallExpr>(Call))
    return Member->getImplicitObjectArgument();
  return isa<CXXOperatorCallExpr>(Call) ? Call->getArg(0) : nullptr;
}

// The type of the object of a member call, looked at through a pointer. The object of `p->get()` is the pointer that `p->` returns.
QualType objectType(const Expr *Object) {
  const QualType Type = Object->IgnoreParenImpCasts()->getType();
  return Type->isPointerType() ? Type->getPointeeType() : Type;
}

// A call that reaches through an owner, a unique_ptr or shared_ptr: its `operator*`, `operator->`, `get`, or the subscript of an array owner.
// The operator of a shared_ptr is a member of its base, so the object is cast. The type of the owner is under the cast.
// `std::to_address` of an owner is no access here. The row `containers` bans it.
bool isOwnerAccess(const CallExpr *Call) {
  const FunctionDecl *Function = Call->getDirectCallee();
  const Expr *Object = Function ? objectOf(Call) : nullptr;
  if (!Object || !isOwner(objectType(Object)))
    return false;
  const OverloadedOperatorKind Operator = Function->getOverloadedOperator();
  return Operator == OO_Star || Operator == OO_Arrow || Operator == OO_Subscript ||
         (Function->getDeclName().isIdentifier() && Function->getName() == "get");
}

bool bindsToName(QualType Type) { return Type->isReferenceType() || Type->isPointerType() || asSpan(Type); }

} // namespace

// A global or a static data member is State. A constant is not: nothing writes it, so it is no second name for anything,
// and a read of it beside a change reads nothing the change can reach. A global that a system header declares, such as `std::cout`, is
// the business of the row iostreams and not of the rules about State. The location decides, not the namespace: a `namespace std`
// that the file opens itself holds state.
bool isMutableGlobal(const VarDecl *Var) {
  return Var->hasGlobalStorage() && !Var->getType().isConstQualified() &&
         !Var->getASTContext().getSourceManager().isInSystemHeader(Var->getLocation());
}

namespace {

// An argument that names an object: it binds to a reference, a pointer or a span, or it is the object of a member call.
struct Arg {
  Walk Where;
  bool Writes;
  bool Object;
  bool ConstRefIntoStd;  // a const reference to a function or class of std, which has no way to reach the State
};

Walk rootsOf(const Expr *E);
void collectArgs(const Expr *Node, llvm::SmallVectorImpl<Arg> &Out);

// The hidden variables of a range-for, and a loop variable that is a reference, are names for the range. The loop variable is
// `*__begin`, and `__begin` is `__range.begin()`, and `__range` is the range expression.
Walk rangeRoots(const VarDecl *Var) {
  const Expr *Init = Var->getInit()->IgnoreParenImpCasts();
  if (Var->isCXXForRangeDecl()) {
    if (const auto *Star = dyn_cast<CXXOperatorCallExpr>(Init); Star && Star->getOperator() == OO_Star)
      return rootsOf(Star->getArg(0));
    if (const auto *Deref = dyn_cast<UnaryOperator>(Init))
      return rootsOf(Deref->getSubExpr());
  } else if (const auto *Call = dyn_cast<CallExpr>(Init)) {
    // The roots are those of the object or the first argument. The handle that the call reaches through is the call's own to say.
    Walk W = objectOf(Call) ? rootsOf(objectOf(Call)) : Call->getNumArgs() ? rootsOf(Call->getArg(0)) : Walk();
    W.ConstHandle |= rootsOf(Init).ConstHandle;
    return W;
  }
  return rootsOf(Init);
}

// A function is in std when it is declared there, or when the call names it there: `std::memcpy` is `::memcpy` that a using
// declaration brings into std, and the call is a call into std.
bool namedInStd(const CallExpr *Call, const FunctionDecl *Function) {
  if (inStdNamespace(Function))
    return true;
  const auto *Ref = dyn_cast<DeclRefExpr>(Call->getCallee()->IgnoreParenImpCasts());
  return Ref && inStdNamespace(Ref->getFoundDecl());
}

// A function that this file does not define, and std does not own, may return a reference, a pointer or a span to any global: it
// reaches the State again. A function that this file defines has had its returns checked, so it returns only what its arguments reach.
bool hiddenReference(const CallExpr *Call, const FunctionDecl *Function) {
  return bindsToName(Function->getReturnType()) && !namedInStd(Call, Function) && !Function->isImplicit() && !Function->isDefaulted() &&
         !Function->isDefined();
}

// ponytail: three ceilings. A reference local is a name of its own, and the row lvalue_references bans it, so the walk does not
// follow it to its initializer. A structured binding is its own root. A call through a function pointer has a fresh root.
// Upgrade: follow the initializer of a reference local and of a binding, and read the type of a function pointer.
Walk rootsOf(const Expr *E) {
  Walk W;
  if (!E)
    return W;
  E = E->IgnoreParens();
  if (const auto *Cast = dyn_cast<CastExpr>(E)) {
    switch (Cast->getCastKind()) {
    case CK_NoOp: case CK_LValueToRValue: case CK_ArrayToPointerDecay: case CK_DerivedToBase: case CK_UncheckedDerivedToBase:
    case CK_BaseToDerived: case CK_Dynamic: case CK_BitCast: case CK_LValueBitCast: case CK_ConstructorConversion:
    case CK_UserDefinedConversion:
      return rootsOf(Cast->getSubExpr());
    default:
      return W;
    }
  }
  if (const auto *Full = dyn_cast<FullExpr>(E))
    return rootsOf(Full->getSubExpr());
  if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(E))
    return rootsOf(Temporary->getSubExpr());
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(E))
    return rootsOf(Default->getExpr());
  if (const auto *Bind = dyn_cast<CXXBindTemporaryExpr>(E))
    return rootsOf(Bind->getSubExpr());
  if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *Var = dyn_cast<VarDecl>(Ref->getDecl())) {
      if (Var->hasInit() && (Var->isImplicit() || (Var->isCXXForRangeDecl() && Var->getType()->isReferenceType())))
        return rangeRoots(Var);
      W.Paths.push_back({{Var}, isMutableGlobal(Var), Ref});
    } else if (isa<BindingDecl>(Ref->getDecl())) {
      W.Paths.push_back({{Ref->getDecl()}, false});
    }
    return W;
  }
  if (isa<CXXThisExpr>(E)) {
    W.Paths.push_back({{&ThisKey}, false});
    return W;
  }
  if (const auto *Member = dyn_cast<MemberExpr>(E)) {
    if (const auto *Var = dyn_cast<VarDecl>(Member->getMemberDecl())) {
      W.Paths.push_back({{Var}, isMutableGlobal(Var), Member});
    } else if (isa<FieldDecl>(Member->getMemberDecl())) {
      W = rootsOf(Member->getBase());
      for (RootPath &Path : W.Paths)
        Path.Steps.push_back(Member->getMemberDecl());
    }
    return W;
  }
  if (const auto *Subscript = dyn_cast<ArraySubscriptExpr>(E))
    return rootsOf(Subscript->getBase());
  if (const auto *Unary = dyn_cast<UnaryOperator>(E)) {
    switch (Unary->getOpcode()) {
    case UO_Deref: case UO_AddrOf: case UO_PreInc: case UO_PreDec: case UO_Extension:
      return rootsOf(Unary->getSubExpr());
    default:
      return W;
    }
  }
  if (const auto *Binary = dyn_cast<BinaryOperator>(E)) {
    if (Binary->isAssignmentOp())
      return rootsOf(Binary->getLHS());
    if (Binary->isCommaOp())
      return rootsOf(Binary->getRHS());
    if (Binary->getType()->isPointerType())
      return rootsOf(Binary->getLHS()->getType()->isPointerType() ? Binary->getLHS() : Binary->getRHS());
    return W;
  }
  if (const auto *Conditional = dyn_cast<AbstractConditionalOperator>(E)) {
    W = rootsOf(Conditional->getTrueExpr());
    W.add(rootsOf(Conditional->getFalseExpr()));
    return W;
  }
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(E))
    return asSpan(Construct->getType()) && Construct->getNumArgs() ? rootsOf(Construct->getArg(0)) : W;
  const auto *Call = dyn_cast<CallExpr>(E);
  const FunctionDecl *Function = Call ? Call->getDirectCallee() : nullptr;
  // An allocation function returns new memory, which no other name reaches.
  if (!Function || Function->isReplaceableGlobalAllocationFunction())
    return W;
  const Expr *Object = objectOf(Call);
  const OverloadedOperatorKind Operator = Function->getOverloadedOperator();
  const bool Deref = Object && isHandle(objectType(Object)) && (Operator == OO_Star || Operator == OO_Arrow);
  if (Object && (Deref || Operator == OO_Subscript || keepsRoot(Function))) {
    W = rootsOf(Object);
    // The owner is const as declared, not as the implicit cast to the const operator makes it. A write through `get()` or
    // through the subscript of an array owner is as much a write through the handle as one through `*`.
    if (isOwnerAccess(Call) && objectType(Object).isConstQualified())
      W.ConstHandle = true;
    return W;
  }
  if (!Object && keepsRoot(Function))
    return Call->getNumArgs() ? rootsOf(Call->getArg(0)) : W;
  if (bindsToName(Function->getReturnType())) {
    // A reference, pointer or span that a function returns reaches only what its arguments and its object reach. The return check
    // refuses a function that returns a global, so no caller receives one. A function from outside this file is the exception.
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(Call, Args);
    for (const Arg &A : Args)
      W.add(A.Where);
    if (hiddenReference(Call, Function)) {
      RootPath Hidden = stateRoot();
      Hidden.At = Call;
      W.Paths.push_back(Hidden);
    }
  }
  return W;
}

// The arguments of a call that name an object: each one that binds to a reference, a pointer or a span, and the object of a
// member call. An argument by value is a copy, so it is no name. A constructor has no object.
void collectArgs(const Expr *Node, llvm::SmallVectorImpl<Arg> &Out) {
  const FunctionDecl *Function = nullptr;
  bool ReadOnly = false;
  llvm::SmallVector<const Expr *, 4> Args;
  if (const auto *Call = dyn_cast<CallExpr>(Node)) {
    Function = Call->getDirectCallee();
    Args.assign(Call->arg_begin(), Call->arg_end());
    if (const Expr *Object = objectOf(Call)) {
      Out.push_back({rootsOf(Object), !cast<CXXMethodDecl>(Function)->isConst(), true, false});
      if (isa<CXXOperatorCallExpr>(Call))
        Args.erase(Args.begin());
    }
  } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(Node)) {
    Function = Construct->getConstructor();
    Args.assign(Construct->arg_begin(), Construct->arg_end());
    // A span of const elements reads what it is made from, though the library takes a non-const reference to make it.
    ReadOnly = asSpan(Construct->getType()) && !isMutableType(Construct->getType());
  }
  if (!Function)
    return;
  for (unsigned I = 0; I < Args.size() && I < Function->getNumParams(); ++I) {
    const QualType Type = Function->getParamDecl(I)->getType();
    if (bindsToName(Type))
      Out.push_back({rootsOf(Args[I]), isMutableType(Type) && !ReadOnly, false,
                     Type->isReferenceType() && Type->getPointeeType().isConstQualified() && inStdNamespace(Function)});
  }
}

} // namespace

// A function that the semantic checks do not judge: the dependent pattern of a template, which is judged at each instantiation where
// every type and every callee is known, and the body of an implicit function, which the compiler wrote. A lambda's call operator is
// implicit and is judged, because the lambda runs where it is written. The state check reads it as a carrier, decision 0037.
// Decision 0036.
bool notJudgedFunction(const FunctionDecl &Node) {
  const auto *Method = dyn_cast<CXXMethodDecl>(&Node);
  return Node.isDependentContext() || (Node.isImplicit() && !(Method && Method->getParent()->isLambda()));
}

namespace {


// The matchers of the semantic checks: a node in a user file, and not in a function that is not judged. The checks read the tree as the
// compiler has it, with the instantiations of a template.
auto judged() { return allOf(unless(isExpansionInSystemHeader()), unless(forFunction(notJudged()))); }

// cplusp-aliasing: decision 0033. When one argument of a call can write, no two arguments reach one object.
// A global bound to a reference, a pointer or a span is refused on its own, because it is the State as well. A const reference
// to a global in a call into std is the one exception: nothing in std can reach the State. A function that returns a reference,
// a pointer or a span may return only what its parameters or `this` reach, else every call of it passes a global.
class AliasingCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(expr(anyOf(callExpr(), cxxConstructExpr()), judged()).bind("call"), this);
    Finder->addMatcher(returnStmt(forFunction(functionDecl(unless(notJudged())).bind("function"))).bind("return"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Return = Result.Nodes.getNodeAs<ReturnStmt>("return")) {
      // A function that returns a reference, a pointer or a span may return only what its parameters or `this` reach. A global,
      // or a reference from a function this file does not define, that escapes this way is a global passed by reference at every
      // call of the function.
      const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("function");
      if (Return->getRetValue() && bindsToName(Function->getReturnType()) &&
          llvm::any_of(rootsOf(Return->getRetValue()).Paths, [](const RootPath &P) { return P.Global || P.Steps[0] == &StateKey; }))
        diag(Return->getBeginLoc(), "a reference to a global escapes");
      return;
    }
    const auto *Node = Result.Nodes.getNodeAs<Expr>("call");
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(Node, Args);
    if (llvm::any_of(Args, [](const Arg &A) {
          return !A.Object && !A.ConstRefIntoStd && llvm::any_of(A.Where.Paths, [](const RootPath &P) { return P.Global; });
        }))
      diag(Node->getBeginLoc(), "a global passed by reference");
    if (!llvm::any_of(Args, [](const Arg &A) { return A.Writes; }))
      return;
    for (size_t I = 0; I < Args.size(); ++I)
      for (size_t J = I + 1; J < Args.size(); ++J)
        if (conflict(Args[I].Where.Paths, Args[J].Where.Paths)) {
          diag(Node->getBeginLoc(), "two names for one object in one call");
          return;
        }
  }
};

// cplusp-return-local: decision 0182. A function that returns a reference, a pointer or a span may not return one to its own local,
// to a parameter by value, to a structured binding by copy or to a capture of a lambda by copy. These die when the function returns.
// The roots are those of the aliasing check: through a call, the object of the call and every argument that binds to a name.
// A root that is a parameter and a handle, a reference, a pointer or a span, is not a local: the object under it lives after the
// call. A local handle is a local. `this`, a static local and a global are not this row's. A global is the row aliasing's.
// ponytail: every argument at a reference parameter counts, also when the callee gives back only its object. Upgrade: read the
// returns of a callee that the file defines. An iterator by value has no roots, so a return through one passes the gate.
// `release()` of a local owner is refused here, though the pointer outlives the owner. The owning raw pointer breaks the limit of
// raw_pointer, and the fix is the same: return the owner by value. Upgrade: a check for `release` under raw_pointer.
class ReturnLocalCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(returnStmt(forFunction(functionDecl(unless(notJudged())).bind("function")), unless(isExpansionInSystemHeader())).bind("return"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Return = Result.Nodes.getNodeAs<ReturnStmt>("return");
    const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("function");
    if (!Return->getRetValue() || !bindsToName(Function->getReturnType()))
      return;
    const auto Dies = [&](const RootPath &P) {
      if (P.Steps[0] == &StateKey || P.Steps[0] == &ThisKey)
        return false;
      const auto *Root = static_cast<const Decl *>(P.Steps[0]);
      // A structured binding by copy is a part of the hidden variable that it decomposes. A binding to a reference is not a local.
      const auto *Binding = dyn_cast<BindingDecl>(Root);
      const auto *Var = Binding ? dyn_cast_or_null<VarDecl>(Binding->getDecomposedDecl()) : dyn_cast<VarDecl>(Root);
      if (!Var || !Var->hasLocalStorage() || (Binding && Var->getType()->isReferenceType()))
        return false;
      if (isa<ParmVarDecl>(Var) && llvm::any_of(P.Steps, [](const void *Step) { return bindsToName(static_cast<const ValueDecl *>(Step)->getType()); }))
        return false;
      if (Var->getDeclContext() == Function)
        return true;
      // A variable of the enclosing function, seen from the body of a lambda: a copy in the closure dies with it.
      const auto *Method = dyn_cast<CXXMethodDecl>(Function);
      return Method && Method->getParent()->isLambda() &&
             llvm::any_of(Method->getParent()->captures(), [&](const LambdaCapture &C) { return C.capturesVariable() && C.getCapturedVar() == Var && C.getCaptureKind() == LCK_ByCopy; });
    };
    if (llvm::any_of(rootsOf(Return->getRetValue()).Paths, Dies))
      diag(Return->getBeginLoc(), "a reference to a local escapes");
  }
};

// A declaration of the library: it is in std, and in a system header. The place decides, not the namespace. A file may open `namespace std`.
bool inLibrary(const Decl *Declaration) {
  return inStdNamespace(Declaration) && Declaration->getASTContext().getSourceManager().isInSystemHeader(Declaration->getLocation());
}

// Whether a type carries a way to write, decisions 0041 and 0043. It reads what the type holds.
// A pointer or a reference to non-const carries one. To const, it carries what its pointee carries. A pointer to a function carries
// nothing. An array carries what its element carries. A record, of the file or of the library, template or not, carries what its fields
// and bases carry. A template of the library also carries what its type arguments carry.
// A container of the library that owns its elements on the heap counts by all its type arguments, decision 0044.
// They are the elements, the comparator, the hasher and the allocator. A copy of it copies each of them.
// So its own pointers are no second name for anything.
// Const reaches the fields, the bases, and the arguments of an owning container. A pointer member of a const record still carries,
// because const does not reach its pointee. A mutable field of a const record carries too, whatever its type.
// A const unique_ptr carries nothing, decision 0042. It cannot be copied, and every use of what it owns is judged as a source of its own.
// A type that the check cannot see whole carries a way to write. An incomplete record is one.
// `Seen` holds the types under judgement, with their qualifiers, and stops a record that holds itself.
using SeenTypes = llvm::SmallDenseSet<QualType, 8>;

bool carriesWrite(QualType Type, SeenTypes &Seen);

bool argumentsCarryWrite(ArrayRef<TemplateArgument> Args, bool Const, SeenTypes &Seen) {
  return llvm::any_of(Args, [&](const TemplateArgument &A) {
    return A.getKind() == TemplateArgument::Pack ? argumentsCarryWrite(A.pack_elements(), Const, Seen)
                                                 : A.getKind() == TemplateArgument::Type &&
                                                       carriesWrite(Const ? A.getAsType().withConst() : A.getAsType(), Seen);
  });
}

bool carriesWrite(QualType Type, SeenTypes &Seen) {
  Type = Type.getCanonicalType();
  if (Type->isPointerType() || Type->isReferenceType()) {
    const QualType Pointee = Type->getPointeeType();
    return !Pointee->isFunctionType() && (!Pointee.isConstQualified() || carriesWrite(Pointee, Seen));
  }
  const bool Const = Type.isConstQualified();
  const auto Held = [&](QualType Member, bool Mutable = false) { return carriesWrite(Const && !Mutable ? Member.withConst() : Member, Seen); };
  if (const auto *Array = Type->getAsArrayTypeUnsafe())
    return Held(Array->getElementType());
  const CXXRecordDecl *Record = Type->getAsCXXRecordDecl();
  if (!Record)
    return false;
  const bool Library = inLibrary(Record), Named = Record->getDeclName().isIdentifier();
  if (Library && Const && Named && Record->getName() == "unique_ptr")
    return false;
  if (!Record->hasDefinition())
    return true;
  if (!Seen.insert(Type).second)
    return false;
  const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Record);
  if (Library && Spec && Named &&
      llvm::is_contained({"basic_string", "vector", "deque", "list", "forward_list", "map", "multimap", "set", "multiset", "unordered_map",
                          "unordered_multimap", "unordered_set", "unordered_multiset"},
                         Record->getName()))
    return argumentsCarryWrite(Spec->getTemplateArgs().asArray(), Const, Seen);
  return llvm::any_of(Record->bases(), [&](const CXXBaseSpecifier &Base) { return Held(Base.getType()); }) ||
         llvm::any_of(Record->fields(),
                      [&](const FieldDecl *Field) { return (Const && Field->isMutable()) || Held(Field->getType(), Field->isMutable()); }) ||
         (Library && Spec && argumentsCarryWrite(Spec->getTemplateArgs().asArray(), Const, Seen));
}

bool givesWrite(QualType Type) {
  SeenTypes Seen;
  return carriesWrite(Type, Seen);
}

// Whether `Argument` is the type `Built`, or one of its template type arguments, all without qualifiers.
bool argumentsInclude(ArrayRef<TemplateArgument> Args, QualType Argument) {
  return llvm::any_of(Args, [&](const TemplateArgument &A) {
    return A.getKind() == TemplateArgument::Pack ? argumentsInclude(A.pack_elements(), Argument)
                                                 : A.getKind() == TemplateArgument::Type &&
                                                       A.getAsType().getCanonicalType().getUnqualifiedType() == Argument;
  });
}

// A value that the library reads without running code of the file. It is a number, or an enum, which has no constructor.
// Or it is a type of the library whose type arguments all count the same way. Decisions 0045 and 0046.
// A type of the file takes its copy through a constructor of its own. That is code of the file, and it may write its argument.
// So does a library type that holds one, because C++23 gives `pair` and `tuple` a constructor that forwards a non-const reference.
// Any other type fails closed.
bool isLibraryValue(QualType Type);

bool argumentsAreLibraryValues(ArrayRef<TemplateArgument> Args) {
  return llvm::all_of(Args, [](const TemplateArgument &A) {
    switch (A.getKind()) {
    case TemplateArgument::Type:
      return isLibraryValue(A.getAsType());
    case TemplateArgument::Pack:
      return argumentsAreLibraryValues(A.pack_elements());
    case TemplateArgument::Integral:
      return true;
    default:
      return false;
    }
  });
}

bool isLibraryValue(QualType Type) {
  Type = Type.getCanonicalType().getUnqualifiedType();
  if (Type->isArithmeticType() || Type->isEnumeralType())
    return true;
  const CXXRecordDecl *Record = Type->getAsCXXRecordDecl();
  if (!Record || !inLibrary(Record))
    return false;
  // A member class, a template or not, holds what the type around it holds, decision 0046.
  // `map<K, V, C>::value_compare` holds the comparator `C`, and `elements_view<V, N>::_Iterator<false>` holds the view `V`.
  const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Record);
  const auto *Outer = dyn_cast<CXXRecordDecl>(Record->getDeclContext());
  return (!Spec || argumentsAreLibraryValues(Spec->getTemplateArgs().asArray())) &&
         (!Outer || isLibraryValue(Record->getASTContext().getRecordType(Outer)));
}

bool isBuiltOrArgument(QualType Argument, QualType Built) {
  Argument = Argument.getCanonicalType().getUnqualifiedType();
  const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Built->getAsCXXRecordDecl());
  return Argument == Built.getCanonicalType().getUnqualifiedType() || (Spec && argumentsInclude(Spec->getTemplateArgs().asArray(), Argument));
}

// A value gives a way to write when it is a non-const lvalue. It does so too when its type carries one, as a const lvalue does.
// A copy of a class that carries no way to write is a read of its value, decision 0041.
bool grantsWrite(const Expr *E) { return (E->isGLValue() && !E->getType().isConstQualified()) || givesWrite(E->getType()); }

// The element access of a sequence of the library on its object: `operator[]`, `at`, `front` and `back`. It gives an element and writes
// nothing, also the non-const one. A span gives a reference to its element from a const call. `std::map` is no sequence: its subscript
// inserts. The place decides, not the namespace, as for the rest of the library.
bool isElementAccess(const FunctionDecl *Function) {
  const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Function);
  const CXXRecordDecl *Owner = Method ? Method->getParent() : nullptr;
  return Owner && Owner->getDeclName().isIdentifier() && inLibrary(Owner) &&
         llvm::is_contained({"array", "vector", "deque", "basic_string", "span"}, Owner->getName()) &&
         (Method->getOverloadedOperator() == OO_Subscript ||
          (Method->getDeclName().isIdentifier() && llvm::is_contained({"at", "front", "back"}, Method->getName())));
}

// An expression that reaches through a const handle. One kind is an access of an owner, as `isOwnerAccess` says.
// Its owner is const as declared, or is itself reached through a const handle.
// The other kind is the name of a reference loop variable of a range-for whose range does. It names an element of the range.
bool reachesThroughConstHandle(const Expr *E) {
  if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
    const auto *Var = dyn_cast<VarDecl>(Ref->getDecl());
    return Var && Var->isCXXForRangeDecl() && Var->getType()->isReferenceType() && rootsOf(Ref).ConstHandle;
  }
  const auto *Call = dyn_cast<CallExpr>(E);
  return Call && isOwnerAccess(Call) && rootsOf(Call).ConstHandle;
}

// Whether a value that reaches through a const handle ends in a use that is no read, decision 0040.
// The value goes up through the nodes that pass it on. They are a bracket, an implicit cast, a member, an element, an address,
// a dereference, an operand, an arm of a conditional, and `std::as_const`.
// It stops where it gives no way to write: a const lvalue that carries none, a number, a pointer to const, a span of const.
// These are reads: a const method on it, a view of const elements, a statement that drops it, and an operand that no code runs.
// A const method on it is a read when its result gives no way to write. A result that gives one is followed from the call.
// Any other use is refused. That is a store, an argument, a return, a capture, a brace list, an explicit cast, and a use that no case knows.
// ponytail: any implicit variable with an initializer is the range of a range-for, which the check of the `for` judges.
// Upgrade: ask whether the variable is the range of a range-for.
bool leaks(ASTContext &Context, const Expr *Node) {
  if (!grantsWrite(Node))
    return false;
  const DynTypedNodeList Parents = Context.getParents(*Node);
  if (Parents.empty())
    return true;
  for (const DynTypedNode &Parent : Parents) {
    const auto *S = Parent.get<Stmt>();
    if (!S) {
      const auto *Var = Parent.get<VarDecl>();
      if ((Parent.get<Decl>() || Parent.get<CXXCtorInitializer>()) && !(Var && Var->isImplicit()))
        return true;
      continue;
    }
    // A method called on the object. A static method reads nothing of it. A non-const method is a use that is no read. A const method and
    // an element access are reads when the result carries no way to write. Else the walk goes on from the call, decision 0041.
    const auto MethodLeaks = [&](const CXXMethodDecl *Method, const CallExpr *Call) {
      return !Method->isStatic() && ((!Method->isConst() && !isElementAccess(Method)) || leaks(Context, Call));
    };
    bool Leak = true;
    if (const auto *Member = dyn_cast<MemberExpr>(S)) {
      if (const auto *Method = dyn_cast<CXXMethodDecl>(Member->getMemberDecl()))
        // The member is the callee. The call is the parent of the member.
        Leak = llvm::any_of(Context.getParents(*Member), [&](const DynTypedNode &Up) {
          return Up.get<CallExpr>() ? MethodLeaks(Method, Up.get<CallExpr>()) : !Method->isStatic();
        });
      else
        Leak = !isa<VarDecl>(Member->getMemberDecl()) && leaks(Context, Member);
    } else if (const auto *Cast = dyn_cast<ExplicitCastExpr>(S)) {
      // A cast of a pointer to an integer is no read. The walk refuses it here, so it need not follow the integer.
      Leak = Cast->getCastKind() == CK_PointerToIntegral || grantsWrite(Cast);
    } else if (const auto *Call = dyn_cast<CallExpr>(S)) {
      // A member operator is a method called on its first operand, as `*h` and `h[i]` are.
      const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getDirectCallee());
      if (Method && !Method->isStatic() && isa<CXXOperatorCallExpr>(Call) && Call->getArg(0) == Node)
        Leak = MethodLeaks(Method, Call);
      else
        Leak = !isAsConst(Call->getDirectCallee()) || leaks(Context, Call);
    } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
      // A constructor of the library that builds a value of the library which carries no way to write, from an lvalue, is a copy.
      // It reads the lvalue, whatever reference the constructor takes. C++23 adds `pair(pair<U1, U2>&)`, and `optional(U&&)` takes
      // a forwarding reference. An xvalue is no read, because a move takes from the object. A function of the library is no constructor:
      // what its result carries says nothing of what it did to its arguments.
      // The argument is of the type that is built, or of one of its type arguments, decision 0044.
      // Another constructor may call a method of the file on what it is given.
      // `std::mt19937` calls `generate` on a seed sequence, and `std::thread` runs a callable.
      // The argument is also a value of the library, decisions 0045 and 0046. `std::optional<W>` forwards a non-const `W&` to the
      // constructors of `W`, and a `W(W&)` of the file may write its argument.
      const CXXRecordDecl *Built = Construct->getType()->getAsCXXRecordDecl();
      const bool Copy = Node->isLValue() && Built && inLibrary(Built) && inLibrary(Construct->getConstructor()) &&
                        isLibraryValue(Node->getType()) && isBuiltOrArgument(Node->getType(), Construct->getType()) &&
                        !givesWrite(Construct->getType());
      Leak = !Copy && (!asSpan(Construct->getType()) || isMutableType(Construct->getType()));
    } else if (const auto *Binary = dyn_cast<BinaryOperator>(S)) {
      // A pointer to member reaches a member that no name shows.
      Leak = Binary->isAssignmentOp() || Binary->getOpcode() == BO_PtrMemD || Binary->getOpcode() == BO_PtrMemI ||
             (!(Binary->isCommaOp() && Binary->getLHS() == Node) && leaks(Context, Binary));
    } else if (const auto *Unary = dyn_cast<UnaryOperator>(S)) {
      Leak = Unary->isIncrementDecrementOp() || Unary->getOpcode() == UO_Coawait || leaks(Context, Unary);
    } else if (const auto *Conditional = dyn_cast<AbstractConditionalOperator>(S)) {
      Leak = Conditional->getCond() != Node && leaks(Context, Conditional);
    } else if (isa<ParenExpr, FullExpr, MaterializeTemporaryExpr, CXXBindTemporaryExpr, ImplicitCastExpr, ArraySubscriptExpr>(S)) {
      Leak = leaks(Context, cast<Expr>(S));
    } else if (const auto *List = dyn_cast<InitListExpr>(S)) {
      // A brace list has two forms. The syntactic one holds the expressions as written, and the semantic one holds them with their
      // conversions, a copy among them. The parent map names the semantic list as the parent of both. The use is the one where the
      // node is an element of the list, which is the semantic form with the conversions applied.
      Leak = llvm::is_contained(List->inits(), Node);
    } else if (const auto *Block = dyn_cast<CompoundStmt>(S)) {
      // The last statement of a statement expression is its value.
      Leak = Block->body_back() == Node && llvm::any_of(Context.getParents(*Block), [](const DynTypedNode &Up) { return Up.get<StmtExpr>(); });
    } else if (isa<IfStmt, WhileStmt, DoStmt, ForStmt, SwitchStmt, CaseStmt, DefaultStmt, LabelStmt, AttributedStmt, UnaryExprOrTypeTraitExpr,
                   CXXNoexceptExpr, CXXTypeidExpr>(S)) {
      Leak = false;
    }
    if (Leak)
      return true;
  }
  return false;
}

// cplusp-const-handle: decisions 0033, 0038 and 0040. A const handle gives reads only.
// The check finds each expression that reaches through a const unique_ptr or shared_ptr.
// It follows the expression up to the first node that is no step of a path. That node is refused unless it is a read.
// `leaks` lists the steps and the reads. The check does not list the ways a write leaves a handle.
// A range-for whose range reaches through a const handle is refused in two cases.
// Its loop variable is a non-const reference, or a value that carries a way to write. Or the compiler's call of `begin` or `end` may change state.
// That is a call outside std, and it is a non-const call on what the handle owns.
class ConstHandleCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(expr(anyOf(callExpr(), declRefExpr()), judged()).bind("source"), this);
    Finder->addMatcher(cxxForRangeStmt(judged()).bind("for"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    if (const auto *Loop = Result.Nodes.getNodeAs<CXXForRangeStmt>("for")) {
      const VarDecl *Variable = Loop->getLoopVariable();
      // A loop variable that is a mutable reference, or a value that carries a way to write, as the proxy of a `vector<bool>` does.
      if (((Variable && (isMutableType(Variable->getType()) || givesWrite(Variable->getType()))) || callsMutableBeginOrEnd(Loop, *Result.SourceManager)) &&
          rootsOf(Loop->getRangeInit()).ConstHandle)
        diag(Loop->getBeginLoc(), "a write through a const handle");
      return;
    }
    const auto *Source = Result.Nodes.getNodeAs<Expr>("source");
    if (reachesThroughConstHandle(Source) && leaks(*Result.Context, Source))
      diag(Source->getBeginLoc(), "a write through a const handle");
  }

private:
  // The compiler's calls of `begin` and `end` on the range are the initializers of `__begin` and `__end`. A callee of the library is a
  // container that the library wrote, and a non-const `begin` of it changes nothing. The location decides, not the namespace: a file may
  // open `namespace std` and declare a `begin` that writes. Any other callee that may change state is refused.
  static bool callsMutableBeginOrEnd(const CXXForRangeStmt *Loop, const SourceManager &SM) {
    for (const Stmt *Part : {Loop->getBeginStmt(), Loop->getEndStmt()}) {
      const auto *Declaration = dyn_cast_or_null<DeclStmt>(Part);
      const auto *Var = Declaration ? dyn_cast_or_null<VarDecl>(Declaration->getSingleDecl()) : nullptr;
      const auto *Call = Var && Var->getInit() ? dyn_cast<CallExpr>(Var->getInit()->IgnoreImplicit()->IgnoreParens()) : nullptr;
      const FunctionDecl *Function = Call ? Call->getDirectCallee() : nullptr;
      if (Function && !SM.isInSystemHeader(Function->getLocation()) && mayChangeState(Function))
        return true;
    }
    return false;
  }
};

// Names in std that return an iterator, a reference, a cast or a new value, and change nothing through their parameters.
// The object or the argument may be non-const. A forwarding reference instantiates as a non-const reference, which is why `make_pair`
// and `get` are here. So `std::sort(v.begin(), v.end())` and `v.front() + v.back()` are no pair of changes by their parameters.
// What their code runs still counts, decision 0038. A copy that `make_pair` makes runs the copy constructor.
// A function of the same name outside std is a change.
bool changesNothing(const FunctionDecl *Function) {
  return inStdNamespace(Function) && Function->getDeclName().isIdentifier() &&
         llvm::is_contained({"begin", "end", "cbegin", "cend", "rbegin", "rend", "crbegin", "crend", "at", "front", "back", "move", "forward",
                             "as_const", "make_pair", "make_tuple", "get", "tie"},
                            Function->getName());
}

// Calls Visit on a node and on everything that runs where the node is written, decision 0038. That is its children, the expression of a
// default argument, the expression of a default member initializer, and the capture initializers of a lambda. It is not the body of
// the lambda, which runs where the lambda is called. An unevaluated operand does not run: `sizeof`, `alignof`, `noexcept` and `typeid`.
// A default argument and a default member initializer have no children of their own, and the code that runs is their expression.
template <typename F> void visitRuns(const Stmt *S, const F &Visit) {
  if (!S || isa<UnaryExprOrTypeTraitExpr, CXXNoexceptExpr, CXXTypeidExpr>(S))
    return;
  Visit(S);
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S))
    visitRuns(Default->getExpr(), Visit);
  else if (const auto *Init = dyn_cast<CXXDefaultInitExpr>(S))
    visitRuns(Init->getExpr(), Visit);
  else if (const auto *Lambda = dyn_cast<LambdaExpr>(S))
    for (const Expr *Capture : Lambda->capture_inits())
      visitRuns(Capture, Visit);
  else
    for (const Stmt *Child : S->children())
      visitRuns(Child, Visit);
}

// A node that changes state: an assignment, an increment, a call of a function that may change state, or a construction
// with a parameter the constructor can write through. A std::span is a view, and cutting one changes nothing, so
// `fill(v, v)` is a matter for the row aliasing. The first part of the rule for a call, a mutable parameter or a non-const method, is
// the callee's own kind. For an operator other than `()` it is an assignment or an increment. The table adds the rest: what the callee
// lists, what its code does, and what an override of it does. The std functions of `changesNothing` are no change by their parameters.
// Their code still counts, through the table.
bool isChange(const Stmt *S) {
  if (const auto *Unary = dyn_cast<UnaryOperator>(S))
    return Unary->isIncrementDecrementOp();
  if (const auto *Binary = dyn_cast<BinaryOperator>(S))
    return Binary->isAssignmentOp();
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
    // A constructor of a system header builds a std object. The compiler builds some of them for a rewritten comparison.
    // The `__unspec` of `o < 5` on an optional is one, and no author wrote it. Its parameters are the library's business.
    // What its code does counts, at any depth, and a line does not stop it.
    // A copy of a container runs the copy constructors of its elements. One of them may write a global with no line to say so.
    const CXXConstructorDecl *Constructor = Construct->getConstructor();
    const bool Library = Constructor->getASTContext().getSourceManager().isInSystemHeader(Constructor->getLocation());
    return !asSpan(Construct->getType()) && ((!Library && hasMutableParameter(Constructor)) || tableChanges(Constructor));
  }
  if (const auto *Call = dyn_cast<CallExpr>(S)) {
    const FunctionDecl *Callee = Call->getDirectCallee();
    if (!Callee)
      return false;
    // An operator other than () is a change by its own kind, an assignment or an increment, so `v[i]` on a non-const vector is none.
    // Whatever the operator, what the callee lists and what its code does count too.
    const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S);
    const bool ByKind = Operator && Operator->getOperator() != OO_Call ? isAssignmentOrIncrement(Operator->getOperator()) : mayChangeState(Callee);
    return (!changesNothing(Callee) && ByKind) || tableChanges(Callee);
  }
  return false;
}

// ponytail: two ceilings. A reference member lets a const method change state, and the check calls that method pure.
// A call through a function pointer or a member pointer has no callee the check can read.
// Upgrade: read the type of a pointer.
bool changes(const Stmt *S) {
  bool Found = false;
  visitRuns(S, [&](const Stmt *Node) { Found = Found || isChange(Node); });
  return Found;
}

// The children of a node that the standard leaves unordered among themselves. Everything else is ordered,
// so two changes in it are not a finding. A coroutine suspend orders its parts. A node kind that is not named here has unordered children.
llvm::SmallVector<const Stmt *, 4> unorderedChildren(const Stmt *S) {
  llvm::SmallVector<const Stmt *, 4> Children;
  if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(S)) {
    // The built-in order of an operator holds when it is overloaded, and for a call, the callee comes first.
    switch (Operator->getOperator()) {
    case OO_Equal: case OO_PlusEqual: case OO_MinusEqual: case OO_StarEqual: case OO_SlashEqual: case OO_PercentEqual:
    case OO_AmpEqual: case OO_PipeEqual: case OO_CaretEqual: case OO_LessLessEqual: case OO_GreaterGreaterEqual:
    case OO_LessLess: case OO_GreaterGreater: case OO_Subscript: case OO_ArrowStar:
    case OO_AmpAmp: case OO_PipePipe: case OO_Comma:
      return Children;
    case OO_Call:
      Children.assign(Operator->arg_begin() + 1, Operator->arg_end());
      return Children;
    default:
      break;
    }
    Children.assign(Operator->arg_begin(), Operator->arg_end());
  } else if (const auto *Call = dyn_cast<CallExpr>(S)) {
    Children.assign(Call->arg_begin(), Call->arg_end());
  } else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S)) {
    if (!Construct->isListInitialization())
      Children.assign(Construct->arg_begin(), Construct->arg_end());
  } else if (const auto *Lambda = dyn_cast<LambdaExpr>(S)) {
    // Only the capture initializers run where the lambda is written. The body runs when it is called.
    Children.assign(Lambda->capture_init_begin(), Lambda->capture_init_end());
  } else if (const auto *Binary = dyn_cast<BinaryOperator>(S)) {
    if (!Binary->isAssignmentOp() && !Binary->isCommaOp() && !Binary->isLogicalOp() && !Binary->isShiftOp() && !Binary->isPtrMemOp())
      Children = {Binary->getLHS(), Binary->getRHS()};
  } else if (!isa<AbstractConditionalOperator>(S) && !isa<ArraySubscriptExpr>(S) && !isa<InitListExpr>(S) && !isa<MemberExpr>(S) &&
             !isa<CoroutineSuspendExpr>(S)) {
    Children.assign(S->child_begin(), S->child_end());
  }
  return Children;
}

// What a subtree writes and what it reads, as root paths, for the read rule of decision 0033. A call may touch the State, so
// any call puts the State in both sets. A global does too. An unevaluated operand and a lambda body do nothing here.
struct Effects {
  Roots Writes, Reads;
};

void addPaths(Roots &Into, const Roots &Paths) {
  for (const RootPath &Path : Paths) {
    Into.push_back(Path);
    if (Path.Global)
      Into.push_back(stateRoot());
  }
}

// A trivial special member, such as the implicit copy of a struct, runs no code.
bool isRealCall(const Stmt *S) {
  const FunctionDecl *Function = nullptr;
  if (const auto *Call = dyn_cast<CallExpr>(S))
    Function = Call->getDirectCallee();
  else if (const auto *Construct = dyn_cast<CXXConstructExpr>(S))
    Function = Construct->getConstructor();
  return !Function || !Function->isTrivial();
}

// What one node adds to the effects. The nodes under it are the visitor's business.
void nodeEffects(const Stmt *S, Effects &E) {
  if (isa<DeclRefExpr, MemberExpr, CXXThisExpr>(S))
    addPaths(E.Reads, rootsOf(cast<Expr>(S)).Paths);
  if (isa<CallExpr, CXXConstructExpr>(S)) {
    if (isRealCall(S)) {
      E.Reads.push_back(stateRoot());
      E.Writes.push_back(stateRoot());
    }
    llvm::SmallVector<Arg, 4> Args;
    collectArgs(cast<Expr>(S), Args);
    for (const Arg &A : Args)
      if (A.Writes)
        addPaths(E.Writes, A.Where.Paths);
  }
  if (const auto *Binary = dyn_cast<BinaryOperator>(S); Binary && Binary->isAssignmentOp())
    addPaths(E.Writes, rootsOf(Binary->getLHS()).Paths);
  if (const auto *Unary = dyn_cast<UnaryOperator>(S); Unary && Unary->isIncrementDecrementOp())
    addPaths(E.Writes, rootsOf(Unary->getSubExpr()).Paths);
}

// The effects of everything that runs where the node is written, the same nodes as `changes` visits.
void effects(const Stmt *S, Effects &E) {
  visitRuns(S, [&](const Stmt *Node) { nodeEffects(Node, E); });
}

// cplusp-evaluation-order: a node with two unordered children that each change state, decision 0026. When exactly one changes
// state, no other unordered child reads what the change can reach, decision 0033.
// The table of the lowered form exists at the end of the translation unit, so the check collects the nodes and judges them then.
class EvaluationOrderCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override {
    startTable();
    Nodes.clear();
  }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(expr(judged()).bind("expr"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (!collectForTable(Result))
      Nodes.push_back(Result.Nodes.getNodeAs<Expr>("expr"));
  }
  void onEndOfTranslationUnit() override {
    for (const Expr *Node : Nodes)
      judge(Node);
  }

private:
  std::vector<const Expr *> Nodes;

  void judge(const Expr *Node) {
    auto Children = unorderedChildren(Node);
    auto Changing = llvm::make_filter_range(Children, [](const Stmt *Child) { return Child && changes(Child); });
    const auto Count = std::distance(Changing.begin(), Changing.end());
    if (Count > 1) {
      diag(Node->getBeginLoc(), "two changes of state without an order");
    } else if (Count == 1) {
      const Stmt *Changer = *Changing.begin();
      Effects Change;
      effects(Changer, Change);
      for (const Stmt *Child : Children) {
        Effects Other;
        if (Child != Changer)
          effects(Child, Other);
        if (conflict(Change.Writes, Other.Reads)) {
          diag(Node->getBeginLoc(), "a read beside an unordered change of state");
          return;
        }
      }
    }
  }
};

// cplusp-inexact-literal: a floating-point literal whose spelling does not convert to its own type without loss.
// The compiler's float library decides. A hex float, 0.5 and 1e3 are exact. 0.1 is not.
class InexactLiteralCheck : public SpelledCheck {
public:
  using SpelledCheck::SpelledCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(floatLiteral().bind("literal"), this); }
  void check(const MatchFinder::MatchResult &Result) override {
    const auto *Literal = Result.Nodes.getNodeAs<FloatingLiteral>("literal");
    SourceLocation Loc = Literal->getBeginLoc();
    // The token as written, also when a macro such as DBL_EPSILON holds it.
    llvm::SmallString<32> Buffer;
    std::string Spelling =
        Lexer::getSpelling(Result.SourceManager->getSpellingLoc(Loc), Buffer, *Result.SourceManager, Result.Context->getLangOpts()).str();
    // A digit separator and a user suffix are no part of the number. Then the suffix f, F, l or L.
    llvm::erase(Spelling, '\'');
    Spelling = Spelling.substr(0, Spelling.find('_'));
    StringRef Text = StringRef(Spelling).rtrim("fFlL");
    // Parse in quad precision first, then convert to the type of the literal. Parsing straight into a double does not report an integer above 2^63 that a
    // double cannot hold, such as 9223372036854775809.0, decision 0027. Either step may lose information.
    llvm::APFloat Value(llvm::APFloat::IEEEquad());
    auto Status = Value.convertFromString(Text, llvm::APFloat::rmNearestTiesToEven);
    if (!Status) {
      llvm::consumeError(Status.takeError());
      return;
    }
    bool LosesInfo = false;
    const llvm::APFloat::opStatus Converted = Value.convert(Result.Context->getFloatTypeSemantics(Literal->getType()), llvm::APFloat::rmNearestTiesToEven, &LosesInfo);
    if ((*Status & llvm::APFloat::opInexact) || (Converted & llvm::APFloat::opInexact) || LosesInfo)
      diag(Result.SourceManager->getFileLoc(Loc), "floating-point literal is not exactly a double");
  }
};

} // namespace

void addSyntaxChecks(ClangTidyCheckFactories &Factories) {
    Factories.registerCheck<MatcherCheck>("cplusp-matcher");
    Factories.registerCheck<MutableCheck>("cplusp-mutable");
    Factories.registerCheck<MultipleInheritanceCheck>("cplusp-multiple-inheritance");
    Factories.registerCheck<ImpureOperatorCheck>("cplusp-impure-operator");
    Factories.registerCheck<IteratorArithmeticCheck>("cplusp-iterator-arithmetic");
    Factories.registerCheck<LambdaLimitsCheck>("cplusp-lambda-limits");
    Factories.registerCheck<EvaluationOrderCheck>("cplusp-evaluation-order");
    Factories.registerCheck<AliasingCheck>("cplusp-aliasing");
    Factories.registerCheck<ReturnLocalCheck>("cplusp-return-local");
    Factories.registerCheck<ConstHandleCheck>("cplusp-const-handle");
    Factories.registerCheck<InexactLiteralCheck>("cplusp-inexact-literal");
}

} // namespace cplusp::detail
