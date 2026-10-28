#include "CplusPChecks.h"

namespace cplusp::detail {

namespace {
// cplusp-tree: decisions 0056 and 0057. The plugin writes the tree of each function the file defines as data, and the core decides
// what it means. One JSON object on one line, appended to the file of the option `Output`, in the shape of the core's types, with names
// as strings. The shell numbers them. This check decides nothing. It keeps every implicit node, and it looks through no cast and no
// parenthesis. A node it has no name for is `{"Unknown": [class, line]}`, and the core refuses it.
// ponytail: a qualified type, a `const int` for one, is `Other`, so the translator refuses it. The slice has no const yet.
// Upgrade: drop the qualifiers that keep the value, once the core has a rule for them.
class TreeWriter {
public:
  // `Claimed` takes the `//@` lines that a loop owns, so the orphan scan skips them.
  // `Structs` takes each plain struct that a type names, by its key, so the check writes it once.
  TreeWriter(ASTContext &Context, std::set<std::pair<unsigned, unsigned>> &Claimed, std::map<std::string, llvm::json::Value> &Structs)
      : Context(Context), SM(Context.getSourceManager()), Mangler(Context.createMangleContext()), Claimed(Claimed), Structs(Structs) {}

  // The key of a function, decision 0058: its Itanium mangled name. The name tells overloads and namespaces apart, and it is the same
  // for a call and for the definition. A function with no mangled name, or one that is templated, a constructor or a destructor, has
  // its qualified name as printed for diagnostics, then `@` and the place of its definition, or of its canonical declaration when it
  // has none. A mangled name has no `@`, so the two kinds never clash.
  std::string key(const FunctionDecl *FD) const {
    if (!FD->isTemplated() && !FD->isDependentContext() && !isa<CXXConstructorDecl>(FD) && !isa<CXXDestructorDecl>(FD) &&
        Mangler->shouldMangleDeclName(FD)) {
      std::string Out;
      llvm::raw_string_ostream OS(Out);
      Mangler->mangleName(GlobalDecl(FD), OS);
      return Out;
    }
    const FunctionDecl *At = FD->getDefinition() ? FD->getDefinition() : FD->getCanonicalDecl();
    const SourceLocation Loc = SM.getFileLoc(At->getLocation());
    return name(FD) + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }
  std::string name(const FunctionDecl *FD) const {
    std::string Out;
    llvm::raw_string_ostream OS(Out);
    FD->getNameForDiagnostic(OS, Context.getPrintingPolicy(), true);
    return Out;
  }

  // ponytail: a function the translator cannot read, a template, a member or one with no body, is written with no signature and no
  // contract, only a body of one `Unknown`. Its return type is `Other` with the opaque kind, so the core refuses its signature by that
  // kind, and a caller sees a callee with no method. Its contract lines still count as claimed.
  // Upgrade: a core rule for these, and their real signature.
  llvm::json::Value function(const FunctionDecl *FD, const Contract &C) const {
    // A trusted function is written with its contract and no body, whatever body it has, decision 0102. `trusted` holds its reason.
    // It is the reason, the file and the line of the declaration with the marker, for the report of prove.
    const std::optional<TrustedMark> Trusted = trustedReason(FD);
    const llvm::json::Value TrustedJson =
        Trusted ? llvm::json::Value(llvm::json::Array{Trusted->Reason, file(Trusted->At->getLocation()), number(line(Trusted->At->getLocation()))})
                : llvm::json::Value(nullptr);
    const CXXMethodDecl *Member = member(FD);
    // A static member function is a free function with the name of its class, `Tally::bump`, and no `this`, decision 0174.
    // One with no contract stays refused as `CXXMethodDecl`, as the tests of decision 0089 pin.
    const CXXMethodDecl *Static = listedStatic(FD) ? cast<CXXMethodDecl>(FD) : nullptr;
    // An interface method is written at its declaration only. A pure virtual function that has a body is none: the body has no rule, decision 0165.
    const bool PureBody = ifaceMethod(FD) && FD->isThisDeclarationADefinition();
    // A const pure virtual function that gives no value has no rule yet, decision 0166. One that writes its object gives its object back, decision 0169.
    const bool NoValue = ifaceMethod(FD) && !PureBody && FD->getReturnType()->isVoidType() && cast<CXXMethodDecl>(FD)->isConst();
    const bool Interface = ifaceMethod(FD) && !PureBody && !NoValue;
    const CXXConstructorDecl *Constructor = valueConstructor(FD);
    const char *Opaque = PureBody                                  ? "a body of a pure virtual function"
                         : NoValue                                   ? "a pure virtual function that gives no value"
                         : FD->isTemplated() && isa<CXXMethodDecl>(FD) && FD->getDescribedFunctionTemplate() ? "a member function template"
                         : noInstance(FD)                            ? "a function template with no instance"
                         : FD->isTemplated()                         ? "FunctionTemplateDecl"
                         : !Constructor && noDestructorMove(FD)       ? "a move constructor in a struct with no destructor"
                         : !Constructor && arrayNoStart(FD)            ? "a std::array field with no start value"
                         : isa<CXXConstructorDecl>(FD) && !Constructor ? "CXXConstructorDecl"
                         : fluentSignature(FD) && FD->getBody() && !fluent(FD) ? "a reference result that is not `*this`"
                         : isa<CXXMethodDecl>(FD) && !Member && !Static && !Constructor ? "CXXMethodDecl"
                         : !FD->getBody() && !Trusted && !Interface && !outOfLineDefault(FD) ? "FunctionDecl without body"
                                                  : nullptr;
    const QualType ValueResult = valueResult(FD);
    llvm::json::Array Params, Conds;
    Enclosing = FD;
    llvm::json::Value Hidden = hiddenConstants(FD);
    if (!Opaque) {
      // A member function takes its object as a parameter `this` by value, first, decision 0089. Its contract lines name it first too.
      // One that is not const writes its object and gives it back, decision 0096.
      if (Member)
        Params.push_back(llvm::json::Array{"this", thisType(Member->getParent(), !Member->isConst())});
      // ponytail: a trusted function that takes `const S&` has the parameter as a value in the model. Decision 0103 promises that its body
      // changes no such parameter, and the gate does not check it: a `const_cast` in a trusted body can break the promise. Upgrade: a gate
      // check of `const_cast` on a parameter or on `this` in a trusted body.
      for (const ParmVarDecl *P : FD->parameters())
        Params.push_back(llvm::json::Array{P->getNameAsString(), paramType(P->getType())});
      Conds = conds(C, Member != nullptr);
      // The `//@` lines in a trusted body belong to it, decision 0103. The walk claims them, and the result is dropped.
      if (Trusted && FD->getBody())
        (void)stmts(FD->getBody());
    }
    // A constructor gives the struct that it builds, decision 0094. Its result type is `This`, and its contract has no `this` parameter.
    if (Constructor)
      return llvm::json::Object{{"name", FD->getNameAsString()},
                                {"key", key(FD)},
                                {"file", file(FD->getLocation())},
                                {"line", number(line(FD->getLocation()))},
                                {"params", std::move(Params)},
                                {"ret", thisType(Constructor->getParent())},
                                {"trusted", TrustedJson},
                                {"hidden", std::move(Hidden)},
                                {"conds", std::move(Conds)},
                                {"body", Trusted ? llvm::json::Array{} : constructorBody(Constructor)}};
    // The destructor is the member `~`, decision 0178.
    llvm::json::Object Out{{"name", Static ? name(FD) : isa<CXXDestructorDecl>(FD) ? std::string("~") : FD->getNameAsString()},
                              {"key", key(FD)},
                              {"file", file(FD->getLocation())},
                              {"line", number(line(FD->getLocation()))},
                              {"params", std::move(Params)},
                              {"ret", Opaque ? tag("Other", Opaque) : FD->getReturnType()->isVoidType() || fluent(FD) ? llvm::json::Value("Void") : !ValueResult.isNull() ? type(ValueResult) : resultType(FD->getReturnType())},
                              {"trusted", TrustedJson},
                              {"interface", Interface},
                              {"hidden", std::move(Hidden)},
                              {"conds", std::move(Conds)},
                              {"body", Opaque ? llvm::json::Array{tag("Unknown", llvm::json::Array{Opaque, number(line(FD->getLocation()))})}
                                       : Trusted || Interface || outOfLineDefault(FD) ? llvm::json::Array{}
                                                 : stmts(FD->getBody())}};
    // The class of a static member function, as the contract of the function reads a bare call, decision 0174.
    if (Static)
      Out["static"] = Static->getParent()->getQualifiedNameAsString();
    // An instance of a function template names its type arguments, and the shell makes `larger'of'int32` of them, decision 0180.
    if (const TemplateArgumentList *Args = FD->getTemplateSpecializationArgs()) {
      llvm::json::Array Of;
      for (const TemplateArgument &Arg : Args->asArray())
        Of.push_back(type(Arg.getAsType()));
      Out["of"] = std::move(Of);
    }
    return Out;
  }

  // A free function template with type parameters only has instances that are functions of the model, decision 0180. Any other template is refused.
  static bool typeOnlyTemplate(const FunctionTemplateDecl *T) {
    if (!T || isa<CXXMethodDecl>(T->getTemplatedDecl()))
      return false;
    for (const NamedDecl *P : *T->getTemplateParameters())
      if (!isa<TemplateTypeParmDecl>(P) || cast<TemplateTypeParmDecl>(P)->isParameterPack())
        return false;
    return true;
  }

  // A function template of the main file that the file never uses, decision 0180. An instance has a body here, or an `extern template` names it. A
  // specialization that overload resolution made and dropped is an implicit instantiation with no body, and it is no instance.
  static bool noInstance(const FunctionDecl *FD) {
    const FunctionTemplateDecl *T = FD->getDescribedFunctionTemplate();
    if (!typeOnlyTemplate(T) || !FD->getASTContext().getSourceManager().isInMainFile(FD->getLocation()))
      return false;
    for (const FunctionDecl *Instance : T->specializations())
      if (Instance->isThisDeclarationADefinition() || Instance->getTemplateSpecializationKind() == TSK_ExplicitInstantiationDeclaration)
        return false;
    return true;
  }

  // The lines in the body of a template that has no instance belong to no function. The walk claims them and drops the result.
  // ponytail: the walk of a dependent body does not reach every statement. A `//@` line of a loop inside a dependent range-for of an unused template is still
  // an orphan. Upgrade: claim each `//@` line in the source range of the body.
  void claimBody(const FunctionDecl *FD) const {
    Enclosing = FD;
    (void)stmts(FD->getBody());
  }

  std::string file(SourceLocation At) const { return SM.getFilename(SM.getFileLoc(At)).str(); }

  // A `constexpr` variable declared at the scope of the file, of any type, or null. A namespace is no scope of the file, nor is a class or a template.
  static const VarDecl *fileConstexpr(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && Var->isConstexpr() && Var->getDeclContext()->isTranslationUnit() && !isa<VarTemplateSpecializationDecl>(Var) && !Var->isTemplated() ? Var : nullptr;
  }
  // The value of a named constant, decision 0106: a `constexpr` variable of an integer type, declared at the scope of the file. Null when
  // the variable is none. A namespace is no scope of the file. A constant of a namespace or of a class can hide one of the file from a
  // function, so `function` writes the names that it hides, decision 0107.
  std::optional<llvm::APSInt> constant(const ValueDecl *D) const {
    const auto *Var = fileConstexpr(D);
    if (!Var)
      return std::nullopt;
    const QualType T = Var->getType().getCanonicalType().getUnqualifiedType();
    const char *S = scalar(T) ? scalar(T) : smallScalar(T);
    const APValue *Value = S && StringRef(S) != "Bool" ? Var->evaluateValue() : nullptr;
    if (!Value || !Value->isInt())
      return std::nullopt;
    return Value->getInt();
  }
  // The value of a named double constant, decision 0158: a `constexpr` variable of type double at the scope of the file, as `constant` takes an integer one.
  std::optional<double> realConstant(const ValueDecl *D) const {
    const auto *Var = fileConstexpr(D);
    if (!Var || !isDouble(Var->getType().getCanonicalType().getUnqualifiedType()))
      return std::nullopt;
    const APValue *Value = Var->evaluateValue();
    if (!Value || !Value->isFloat())
      return std::nullopt;
    return Value->getFloat().convertToDouble();
  }
  // Whether a scope declares a name, or a using-directive of the scope brings one in, decision 0107. A function holds its locals in its list of
  // declarations, not in its table of names, so its list is read. `Seen` stops a cycle of directives. The table of the translation unit holds the
  // constants of the file themselves, so `Own` is false for it: only its directives count.
  // ponytail: a function's locals, and the later declarations of a namespace, hide the name from the whole function. This refuses some correct
  // programs. Upgrade: look up from the point of the declaration.
  static bool declares(const DeclContext *DC, DeclarationName Name, std::set<const DeclContext *> &Seen, bool Own = true) {
    DC = DC->getPrimaryContext();
    if (!Seen.insert(DC).second)
      return false;
    if (isa<FunctionDecl>(DC)) {
      for (const Decl *D : DC->decls()) {
        if (const auto *Named = dyn_cast<NamedDecl>(D); Named && Named->getDeclName() == Name)
          return true;
      }
      // ponytail: a using-directive in a function body is not looked through. The gate bans it in verified and trusted code. Upgrade: find
      // each UsingDirectiveDecl in the DeclStmts of the body.
      return false;
    }
    if (Own && !DC->lookup(Name).empty())
      return true;
    for (const UsingDirectiveDecl *Using : DC->using_directives())
      if (Using->getNominatedNamespace() && declares(Using->getNominatedNamespace(), Name, Seen))
        return true;
    return false;
  }
  // The names of the constants of the file that C++ does not find from the function, decision 0107. Unqualified lookup goes out from the function
  // through its class, the bases of the class, the functions and namespaces around it, and the using-directives of each, to the file. A name that one
  // of them declares hides the constant of the file, and so does a directive of the file that brings in the same name: it has two meanings then.
  llvm::json::Array hiddenConstants(const FunctionDecl *FD) const {
    llvm::json::Array Out;
    for (const Decl *D : Context.getTranslationUnitDecl()->decls()) {
      const auto *Var = dyn_cast<VarDecl>(D);
      if (!Var || !Var->isConstexpr() || !(constant(Var) || realConstant(Var)))
        continue;
      const DeclarationName Name = Var->getDeclName();
      bool Hidden = false;
      for (const DeclContext *DC = FD->getDeclContext(); DC && !DC->isTranslationUnit() && !Hidden; DC = DC->getParent()) {
        std::set<const DeclContext *> Seen;
        Hidden = declares(DC, Name, Seen);
        if (const auto *RD = dyn_cast<CXXRecordDecl>(DC); RD && !Hidden && RD->hasDefinition())
          Hidden = !RD->forallBases([&](const CXXRecordDecl *Base) {
            std::set<const DeclContext *> BaseSeen;
            return !declares(Base, Name, BaseSeen);
          });
      }
      std::set<const DeclContext *> Seen;
      // An inline namespace puts its names in the table of its parent and makes no directive, so a second declaration of the name in the table of the
      // file is one of an inline namespace.
      const DeclContext::lookup_result AtFile = Context.getTranslationUnitDecl()->lookup(Name);
      if (Hidden || std::distance(AtFile.begin(), AtFile.end()) > 1 || declares(Context.getTranslationUnitDecl(), Name, Seen, false))
        Out.push_back(Var->getNameAsString());
    }
    // The words of a contract hide a name of C++, decision 0158. A word that C++ finds from the function as a name is listed, so a contract line that reads
    // the word is refused. C++ looks from the function through its parameters and locals, its class and the bases of the class, the namespaces around it
    // and the file. An out-of-line member is looked up in its class, because the semantic context is the class.
    for (const char *Word : {"eps", "eta", "DBL_MAX"}) {
      const DeclarationName Name = &Context.Idents.get(Word);
      std::set<const DeclContext *> Seen;
      bool Found = declares(FD, Name, Seen);
      // The semantic context, and the lexical one when it differs: the body of a friend that a class defines is looked up in the class.
      for (const DeclContext *Start : {FD->getDeclContext(), FD->getLexicalDeclContext()}) {
        for (const DeclContext *DC = Start; DC && !Found; DC = DC->getParent()) {
          std::set<const DeclContext *> Visited;
          Found = declares(DC, Name, Visited);
          if (const auto *RD = dyn_cast<CXXRecordDecl>(DC); RD && !Found && RD->hasDefinition())
            Found = !RD->forallBases([&](const CXXRecordDecl *Base) {
              std::set<const DeclContext *> BaseSeen;
              return !declares(Base, Name, BaseSeen);
            });
        }
      }
      if (Found)
        Out.push_back(Word);
    }
    return Out;
  }
  // Writes the item of an enum class of the file, so a contract can name its enumerators though no code names its type, decision 0114.
  void writeEnum(const EnumDecl *ED) const {
    if (plainEnum(Context.getTypeDeclType(ED)))
      enumType(ED);
    else if (valuedEnum(Context.getTypeDeclType(ED)))
      valuedType(ED);
  }
  // The line of the tree for a named constant, or null.
  llvm::json::Value constantLine(const VarDecl *Var) const {
    // A double constant has a line when its value is `m / q`, decision 0158: the sign, `m` and `q`.
    if (const std::optional<double> Real = realConstant(Var)) {
      uint64_t M, Q;
      if (!std::isfinite(*Real) || !dyadic(std::fabs(*Real), M, Q))
        return nullptr;
      return llvm::json::Object{{"constant", Var->getNameAsString()}, {"real", llvm::json::Array{std::signbit(*Real) && *Real != 0.0, number(M), number(Q)}}};
    }
    const std::optional<llvm::APSInt> Value = constant(Var);
    if (!Value)
      return nullptr;
    llvm::SmallString<32> Text;
    Value->toString(Text);
    return llvm::json::Object{{"constant", Var->getNameAsString()}, {"value", std::string(Text)}};
  }
  // The line of the tree for a mutable global or a static data member that the file defines, decision 0173: its name and its type. The shell
  // lists them in this order, which is the order of the definitions.
  llvm::json::Value globalLine(const VarDecl *Var) const {
    if (!isGlobal(Var) || !Var->isThisDeclarationADefinition())
      return nullptr;
    return llvm::json::Object{{"global", nameOf(Var)}, {"ty", type(Var->getType())}};
  }
  // A mutable global or static data member, not a function-local static and not a name of the standard library, decision 0173.
  static bool isGlobal(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && isMutableGlobal(Var) && !Var->isStaticLocal() && !Var->isInStdNamespace();
  }
  // The name of a variable in the tree. A static data member has its qualified name as one word, `Registry::last_id`, decision 0173.
  static std::string nameOf(const ValueDecl *D) {
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && Var->isStaticDataMember() ? Var->getQualifiedNameAsString() : D->getNameAsString();
  }

private:
  ASTContext &Context;
  const SourceManager &SM;
  std::unique_ptr<MangleContext> Mangler;
  std::set<std::pair<unsigned, unsigned>> &Claimed;
  std::map<std::string, llvm::json::Value> &Structs;
  mutable std::set<const CXXRecordDecl *> Visiting;  // the structs whose fields `plainStruct` is reading
  mutable bool InConstructorBody = false;  // `constructorBody` is writing the statements of a body, where a field and `this` have no rule, decision 0179
  mutable const FunctionDecl *Enclosing = nullptr;  // the function that `function` is writing, the floor of a loop's walk upward
  mutable const Stmt *HoistFor = nullptr;  // the statement that may take the steps of a chain before it, decision 0183, or null
  mutable const Expr *HoistOk = nullptr;   // the call whose object is a chain that may go before `HoistFor`
  mutable llvm::json::Array Prelude;       // the statements that run before `HoistFor`: the fresh local of a temporary and the steps of a chain
  mutable unsigned Chains = 0;             // the count of the fresh locals `'chain'<n>`

  // The contract lines as data. A line of a loop has no parameters.
  llvm::json::Array conds(const Contract &C, bool Member = false) const {
    llvm::json::Array Out;
    for (const Contract::Line &L : C.Lines) {
      llvm::json::Array Names;
      if (Member)
        Names.push_back("this");
      for (const std::string &N : L.Params)
        Names.push_back(N);
      // The word ends at any white space.
      const StringRef Text = L.Text;
      const size_t Cut = Text.find_first_of(" \t\f\v\r");
      Out.push_back(llvm::json::Object{
          {"kind", Text.substr(0, Cut).str()}, {"file", file(SM.getLocForStartOfFile(L.Id))}, {"line", number(L.Number)}, {"text", Cut == StringRef::npos ? "" : Text.substr(Cut).trim().str()},
          {"params", std::move(Names)}});
    }
    return Out;
  }
  // The `//@` lines directly above a loop, claimed for it. They stop at the start of the body of the function, so a loop on the line of
  // its function leaves the function its lines.
  llvm::json::Array loopConds(const Stmt *Loop) const {
    Contract C = linesAbove(Loop);
    for (const Contract::Line &L : C.Lines)
      Claimed.insert({L.File, L.Number});
    // An assert or apply line above a loop is a statement before it, `bodyLines`. The loop keeps its invariant and decreases lines.
    C.Lines.erase(std::remove_if(C.Lines.begin(), C.Lines.end(), isBodyLine), C.Lines.end());
    return conds(C);
  }
  // The `//@` lines directly above a statement, up to the start of the body of the function.
  Contract linesAbove(const Stmt *S, bool SkipComments = false) const {
    const Stmt *Body = Enclosing ? Enclosing->getBody() : nullptr;
    return contractAbove(SM, S->getBeginLoc(), Body ? Body->getBeginLoc() : SourceLocation(), SkipComments);
  }
  // Whether only white space is before the statement on its line. A statement after code, as the `if` of `} else if`, takes no line above.
  bool startsItsLine(const Stmt *S) const {
    const SourceLocation At = SM.getExpansionLoc(S->getBeginLoc());
    if (At.isInvalid())
      return false;
    const auto [File, Offset] = SM.getDecomposedLoc(At);
    bool Invalid = false;
    const StringRef Text = SM.getBufferData(File, &Invalid);
    if (Invalid)
      return false;
    const size_t Newline = Text.substr(0, Offset).rfind('\n');
    return Text.slice(Newline == StringRef::npos ? 0 : Newline + 1, Offset).trim().empty();
  }
  static bool isBodyLine(const Contract::Line &L) {
    const StringRef Text = L.Text;
    const StringRef Word = Text.substr(0, Text.find_first_of(" \t\f\v\r"));
    return Word == "assert" || Word == "apply";
  }
  // The assert and apply lines directly above a statement, as statements of their own, decision 0099. A line that an outer statement on
  // the same line took first is not taken again.
  void bodyLines(const Stmt *S, llvm::json::Array &Out) const {
    if (!startsItsLine(S))
      return;
    Contract C = linesAbove(S, true);
    // A line that is no assert or apply line is dropped, and so is one that was taken already.
    C.Lines.erase(std::remove_if(C.Lines.begin(), C.Lines.end(), [&](const Contract::Line &L) { return !isBodyLine(L) || !Claimed.insert({L.File, L.Number}).second; }),
                  C.Lines.end());
    for (const Contract::Line &L : C.Lines) {
      Contract One;
      One.Lines.push_back(L);
      llvm::json::Value Cond = std::move(conds(One).front());
      Out.push_back(tag(StringRef(L.Text).starts_with("assert") ? "Assert" : "Apply", std::move(Cond)));
    }
  }

  static llvm::json::Value number(uint64_t N) { return llvm::json::Value(N); }
  unsigned line(SourceLocation At) const { return SM.getExpansionLineNumber(At); }
  static llvm::json::Value tag(const char *Name, llvm::json::Value Inner) { return llvm::json::Object{{Name, std::move(Inner)}}; }
  // A node with no valid place, a default argument, takes the line of the call or statement around it.
  llvm::json::Value unknown(const Stmt *S, const std::string &What, unsigned Near) const {
    return tag("Unknown", llvm::json::Array{What, number(S->getBeginLoc().isValid() ? line(S->getBeginLoc()) : Near)});
  }
  // What the bot reads for a node with no rule. An expression statement and the same expression inside another give the same words.
  static std::string describe(const Stmt *S) {
    // A statement that makes a temporary, such as `r = x;` on an optional, is wrapped for its cleanups. The wrapper is not the construct.
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(S))
      return describe(Cleanups->getSubExpr());
    if (const auto *Binary = dyn_cast<BinaryOperator>(S))
      return std::string("BinaryOperator ") + Binary->getOpcodeStr().str();
    if (const auto *Unary = dyn_cast<UnaryOperator>(S))
      return std::string("UnaryOperator ") + UnaryOperator::getOpcodeStr(Unary->getOpcode()).str();
    return S->getStmtClassName();
  }

  // The scalar of the subset that a type is, as the core names it, or null. A qualified type is none.
  const char *scalar(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (Canon.hasQualifiers())
      return nullptr;
    if (const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr())) {
      const uint64_t Bits = Context.getTypeSize(Canon);
      switch (Builtin->getKind()) {
      case BuiltinType::Int:
        return Bits == 32 ? "I32" : nullptr;
      case BuiltinType::Long:
      case BuiltinType::LongLong:
        return Bits == 64 ? "I64" : nullptr;
      case BuiltinType::UChar:
        return "U8";
      case BuiltinType::UInt:
        return Bits == 32 ? "U32" : nullptr;
      case BuiltinType::ULong:
      case BuiltinType::ULongLong:
        return Bits == 64 ? "U64" : nullptr;
      case BuiltinType::Bool:
        return "Bool";
      default:
        return nullptr;
      }
    }
    return nullptr;
  }

  // The small integer types of decision 0106: `int8_t`, `int16_t` and `uint16_t`, or null. They are types of the subset, but no element of a
  // sequence and no value of an optional, so `scalar` does not name them. They can be a field, decision 0138.
  const char *smallScalar(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (Canon.hasQualifiers())
      return nullptr;
    if (const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr())) {
      const uint64_t Bits = Context.getTypeSize(Canon);
      switch (Builtin->getKind()) {
      case BuiltinType::SChar:
        return Bits == 8 ? "I8" : nullptr;
      case BuiltinType::Short:
        return Bits == 16 ? "I16" : nullptr;
      case BuiltinType::UShort:
        return Bits == 16 ? "U16" : nullptr;
      default:
        return nullptr;
      }
    }
    return nullptr;
  }

  // Whether a type is `double` with no qualifier, decision 0150. `float` and `long double` are refused by the gate.
  static bool isDouble(QualType T) {
    const QualType Canon = T.getCanonicalType();
    const auto *Builtin = dyn_cast<BuiltinType>(Canon.getTypePtr());
    return !Canon.hasQualifiers() && Builtin && Builtin->getKind() == BuiltinType::Double;
  }

  // The element type of a read-only sequence, decision 0064, or null: a const vector or a reference to one, except `std::vector<bool>`, and
  // a span of const elements, any extent, and a const std::array, decision 0132. A reference is looked through. The element is a scalar or a plain struct, decision 0076. A
  // `Field` is a field of a struct, decision 0076: a vector with no const, and no span.
  QualType seqElement(QualType T, bool Field = false) const {
    const bool Reference = T->isReferenceType();
    if (Reference)
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (!Spec || !Spec->isInStdNamespace() || Spec->getTemplateArgs().size() == 0 || Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    if (Spec->getName() == "vector") {
      if (!(Field || T.isConstQualified()) || Elem.getCanonicalType().hasQualifiers())
        return QualType();
      const char *S = scalar(Elem);
      // A unique_ptr of a struct or an interface is an element of a vector, not of a field, decision 0170.
      if (!Field && !ownVecElement(Elem).isNull())
        return Elem;
      return (S ? StringRef(S) != "Bool" : plainStruct(Elem) != nullptr) ? Elem : QualType();
    }
    // A `std::array<T, N>` field of a scalar other than bool is a sequence of length N, decision 0196.
    if (Field && Spec->getName() == "array")
      return fieldArray(T);
    if (!Field && Spec->getName() == "span" && Elem.isConstQualified()) {
      Elem.removeLocalConst();
      return scalar(Elem) || (!Elem.getCanonicalType().hasQualifiers() && plainStruct(Elem)) ? Elem : QualType();
    }
    // A const std::array of a scalar or a plain struct is a sequence of fixed length, decision 0132. The plugin passes an array of bool on, and the core
    // refuses it, decision 0136.
    // A std::array by value is a copy that only the function sees, so it is a read-only sequence too, decision 0175.
    if (!Field && Spec->getName() == "array" && (T.isConstQualified() || !Reference) && !T.isVolatileQualified() && !Elem.getCanonicalType().hasQualifiers())
      return scalar(Elem) || plainStruct(Elem) ? Elem : QualType();
    return QualType();
  }
  bool isSeq(QualType T) const { return !seqElement(T).isNull(); }
  // The element of a `std::array<T, N>` field, or null: a scalar `T` other than bool, no qualifier, and a length that fits, decision 0196.
  QualType fieldArray(QualType T) const {
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (T->isReferenceType() || T.hasQualifiers() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "array" || Spec->getTemplateArgs().size() != 2 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type || seqExtent(T).getAsNull())
      return QualType();
    const QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    const char *S = scalar(Elem);
    return !Elem.getCanonicalType().hasQualifiers() && S && StringRef(S) != "Bool" ? Elem : QualType();
  }
  // The element of a sequence field that a member function reads and writes: a vector, decision 0187, or a `std::array`, decision 0196.
  QualType fieldSeq(QualType T) const { return localVec(T).isNull() ? fieldArray(T) : localVec(T); }
  // Whether an initializer is the zeros of a value-initialized `std::array`: `f()`, `f{}`, `{}`, `{{}}`, and a value-initialized temporary `std::array<T, N>()`, also as a default member initializer, decision 0196.
  static bool arrayZeros(const Expr *E) {
    E = E->IgnoreParenImpCasts();
    if (const auto *Default = dyn_cast<CXXDefaultInitExpr>(E))
      return arrayZeros(Default->getExpr());
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E))
      return Construct->getNumArgs() == 0 && Construct->requiresZeroInitialization();
    if (isa<ImplicitValueInitExpr>(E))
      return true;
    if (const auto *List = dyn_cast<InitListExpr>(E)) {
      for (const Expr *One : List->inits())
        if (!arrayZeros(One))
          return false;
      return true;
    }
    return false;
  }
  // A vector field of the object that a member function writes: a read of it is a read of the sequence, as in a const member, decision 0187.
  bool isFieldVec(const Expr *E) const {
    const FieldDecl *Field = objectField(E->IgnoreParenImpCasts());
    return Field && !fieldSeq(Field->getType()).isNull();
  }

  // The fixed extent of a read-only sequence, decisions 0070 and 0132, or null: a vector, and a span of `std::dynamic_extent`. A std::array has its length.
  llvm::json::Value seqExtent(QualType T) const {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (!Spec || (Spec->getName() != "span" && Spec->getName() != "array") || Spec->getTemplateArgs().size() < 2 || Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Integral)
      return nullptr;
    llvm::APSInt N = Spec->getTemplateArgs()[1].getAsIntegral();
    return N.isNegative() || N.getActiveBits() > 63 || N.isAllOnes() ? llvm::json::Value(nullptr) : llvm::json::Value(static_cast<int64_t>(N.getZExtValue()));
  }

  // The element of a `std::optional` of a scalar or of a plain struct, decisions 0075 and 0137, or null: by value, or by const lvalue
  // reference. A write handle, a volatile optional and an optional of anything else are none.
  QualType optType(QualType T) const {
    if (T->isReferenceType()) {
      if (!T->isLValueReferenceType() || !T->getPointeeType().isConstQualified())
        return QualType();
      T = T->getPointeeType();
    }
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    if (T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "optional" || Spec->getTemplateArgs().size() != 1 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    const QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    // The element is a scalar, or a plain struct with no qualifier, decision 0137.
    return scalar(Elem) || (!Elem.getCanonicalType().hasQualifiers() && plainStruct(Elem)) ? Elem : QualType();
  }

  // The scalar of an optional of a scalar, or null. A field of a struct may hold such an optional, and no other.
  const char *optElement(QualType T) const {
    const QualType Elem = optType(T);
    return Elem.isNull() ? nullptr : scalar(Elem);
  }
  // Whether a type is an optional of a scalar or of a plain struct.
  bool isOpt(QualType T) const { return !optType(T).isNull(); }

  // The element of a `std::unique_ptr` that the code only reads, decision 0142, or null: `std::unique_ptr<T>` with the default deleter, for a
  // scalar or a plain struct with no qualifier. The type of a value or of a name that reads one, so no reference.
  QualType ownElement(QualType T) const {
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T.getUnqualifiedType()->getAsCXXRecordDecl());
    if (T->isReferenceType() || T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "unique_ptr" ||
        Spec->getTemplateArgs().size() != 2 || Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type ||
        Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Type)
      return QualType();
    const QualType Elem = Spec->getTemplateArgs()[0].getAsType();
    const CXXRecordDecl *Deleter = Spec->getTemplateArgs()[1].getAsType()->getAsCXXRecordDecl();
    if (!Deleter || !Deleter->isInStdNamespace() || Deleter->getName() != "default_delete")
      return QualType();
    // A scalar, a plain struct, or an interface, decision 0168.
    return !Elem.getCanonicalType().hasQualifiers() && (scalar(Elem) || plainStruct(Elem) || isInterface(Elem->getAsCXXRecordDecl())) ? Elem : QualType();
  }
  bool isOwn(QualType T) const { return !ownElement(T).isNull(); }
  // A `std::unique_ptr` of a struct or an interface with no qualifier, as the element of a vector, decision 0170, or null.
  QualType ownVecElement(QualType Elem) const {
    if (Elem.isNull() || Elem.getCanonicalType().hasQualifiers())
      return QualType();
    const QualType Pointee = ownElement(Elem);
    return !Pointee.isNull() && Pointee->getAsCXXRecordDecl() ? Elem : QualType();
  }
  // The type of an element of a sequence for the core. A unique_ptr is `Own` of its key, and any other element is its type, decision 0170.
  llvm::json::Value elementType(QualType Elem) const {
    if (const QualType Held = ownVecElement(Elem); !Held.isNull())
      {
      (void)ownScalar(ownElement(Held));  // writes the struct or the interface
      return tag("Own", structKey(ownElement(Held)->getAsCXXRecordDecl()->getDefinition()));
    }
    return type(Elem);
  }
  // Whether a type is a `std::unique_ptr` of any class.
  static bool isUniquePtr(QualType T) {
    const CXXRecordDecl *RD = T.getNonReferenceType()->getAsCXXRecordDecl();
    return RD && RD->isInStdNamespace() && RD->getIdentifier() && RD->getName() == "unique_ptr";
  }
  // The element of a unique_ptr as the type of the model: an interface is a `Struct` of its key, decision 0168.
  llvm::json::Value ownScalar(QualType Elem) const {
    if (const CXXRecordDecl *RD = Elem->getAsCXXRecordDecl(); RD && isInterface(RD)) {
      interfaceEntry(RD);
      return tag("Struct", structKey(RD->getDefinition()));
    }
    return type(Elem);
  }

  // The plain struct that a type is, decision 0073, or null. A const and a reference are looked through. Plain means a definition with
  // a name, no bases, no virtual function, no destructor and no member template, and fields that are each a scalar, a small integer
  // type (decision 0138), a plain enum (decision 0109), a plain struct, an optional of a scalar (decision 0075) or a sequence (decision
  // 0076), with no const, no reference and no bit field. Member
  // functions, static members and access do not matter, decision 0089. Nor do constructors, decision 0094: a constructor that is no
  // value constructor is refused where it is written.
  const CXXRecordDecl *plainStruct(QualType T) const {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const CXXRecordDecl *RD = T.isVolatileQualified() ? nullptr : T->getAsCXXRecordDecl();
    if (!RD || !RD->hasDefinition())
      return nullptr;
    RD = RD->getDefinition();
    if (RD->isUnion() || RD->isLambda() || !RD->getIdentifier() || RD->isDependentContext() || (isa<ClassTemplateSpecializationDecl>(RD) && !namedInstance(RD)) ||
        ((RD->getNumBases() || RD->isPolymorphic()) && !finalOverInterface(RD)))
      return nullptr;
    // A member function, a static member and a private field do not change the value of the struct, decision 0089. A member template still has no rule, decision 0089.
    // An instance of a class template keeps its member template, which is refused at the template, decision 0188.
    for (const Decl *D : RD->decls())
      if (isa<FunctionTemplateDecl>(D) && !isa<ClassTemplateSpecializationDecl>(RD))
        return nullptr;
    // A struct that holds a sequence of itself is in its own fields: assume it is plain there, decision 0076.
    if (!Visiting.insert(RD).second)
      return RD;
    bool Plain = true;
    for (const FieldDecl *F : RD->fields()) {
      const QualType FT = F->getType();
      if (F->isBitField() || FT->isReferenceType() || FT.hasQualifiers() ||
          (!scalar(FT) && !smallScalar(FT) && !plainEnum(FT) && !plainStruct(FT) && !optElement(FT) && seqElement(FT, true).isNull() && ownVecElement(FT).isNull())) {
        Plain = false;
        break;
      }
    }
    Visiting.erase(RD);
    return Plain ? RD : nullptr;
  }

  // Whether an expression reads the object, through `this`, implicit or written. A field of another object does not.
  static bool readsObject(const Stmt *S) {
    if (!S)
      return false;
    if (isa<CXXThisExpr>(S))
      return true;
    for (const Stmt *Child : S->children())
      if (readsObject(Child))
        return true;
    return false;
  }

  // A move constructor that the file defines, in a plain struct with no destructor of its own, decision 0179. C++ also runs it at `return x;`, for a parameter
  // by value and in a vector, where the model has no call, so it has no rule.
  bool noDestructorMove(const FunctionDecl *FD) const {
    const FunctionDecl *Def = nullptr;
    if (!isa<CXXConstructorDecl>(FD) || !FD->hasBody(Def))
      return false;
    const auto *C = cast<CXXConstructorDecl>(Def);
    // The struct table lists a destructor only when `member` holds, so a destructor `= default` is none.
    const CXXDestructorDecl *D = C->getParent()->getDestructor();
    return C->isMoveConstructor() && !C->isTemplated() && !C->isDeleted() && !C->isDefaulted() && !(D && member(D)) &&
           plainStruct(Context.getRecordType(C->getParent()));
  }

  // A move constructor `= default` of a plain struct with a destructor of the model, whose fields are each a scalar or a `std::unique_ptr`, decision 0197. It moves each
  // `std::unique_ptr` field and copies each scalar field. A field of any other type has no rule.
  bool defaultedMove(const CXXConstructorDecl *C) const {
    if (!C->isDefaulted() || !C->isExplicitlyDefaulted() || C->isImplicit() || C->isDeleted() || !C->isMoveConstructor() || C->getNumParams() != 1 || C->isTemplated() || C->getDescribedFunctionTemplate())
      return false;
    const CXXRecordDecl *RD = C->getParent();
    if (RD->getNumBases() != 0 || !plainStruct(Context.getRecordType(RD)))
      return false;
    const CXXDestructorDecl *D = RD->getDestructor();
    if (!(D && member(D)))
      return false;
    for (const FieldDecl *F : RD->fields())
      if (ownVecElement(F->getType()).isNull() && !scalar(F->getType()) && !smallScalar(F->getType()))
        return false;
    return true;
  }
  // `f(std::move(other.f))` of a move constructor: the field of the parameter `other` that the init moves into the `std::unique_ptr` field `F`, or null for any other form,
  // decision 0197.
  const FieldDecl *movedFrom(const Expr *Init, const FieldDecl *F, const CXXConstructorDecl *C) const {
    const auto *Construct = dyn_cast<CXXConstructExpr>(Init->IgnoreParenImpCasts());
    if (!C->isMoveConstructor() || C->getNumParams() != 1 || !Construct || Construct->getNumArgs() != 1 || !Construct->getConstructor()->isMoveConstructor() || ownVecElement(F->getType()).isNull())
      return nullptr;
    const auto *Move = dyn_cast<CallExpr>(Construct->getArg(0)->IgnoreParenImpCasts());
    if (!Move || Move->getNumArgs() != 1 || !Move->getDirectCallee() || !Move->getDirectCallee()->isInStdNamespace() || !Move->getDirectCallee()->getDeclName().isIdentifier() ||
        Move->getDirectCallee()->getName() != "move")
      return nullptr;
    const auto *Member = dyn_cast<MemberExpr>(Move->getArg(0)->IgnoreParenImpCasts());
    const auto *Base = Member && !Member->isArrow() ? dyn_cast<DeclRefExpr>(Member->getBase()->IgnoreParenImpCasts()) : nullptr;
    const auto *From = Member ? dyn_cast<FieldDecl>(Member->getMemberDecl()) : nullptr;
    if (!Base || !From || Base->getDecl() != C->getParamDecl(0) || From->getParent() != C->getParent() ||
        From->getType().getCanonicalType() != F->getType().getCanonicalType())
      return nullptr;
    return From;
  }

  // A constructor that is written as a function, decision 0094: a constructor of a plain struct that is no copy constructor,
  // delegates to none, and gives each field exactly one value in its member init list. It can have a body and be a move constructor, decision 0179. A vector field that the
  // list leaves out, with no default member initializer, starts empty, decision 0187. Any other field that the list leaves out has no rule. Null for any other function. A constructor that is only declared is looked up by its definition.
  const CXXConstructorDecl *valueConstructor(const FunctionDecl *FD) const {
    const FunctionDecl *Def = nullptr;
    if (!isa<CXXConstructorDecl>(FD))
      return nullptr;
    // A move constructor `= default` has a body only when the file uses it, so its definition is found by the declaration, decision 0197.
    if (!FD->hasBody(Def)) {
      Def = FD->getDefinition();
      if (!Def || !Def->isDefaulted())
        return nullptr;
    }
    const auto *C = cast<CXXConstructorDecl>(Def);
    if (C->isDefaulted())
      return defaultedMove(C) ? C : nullptr;
    if (noDestructorMove(C))
      return nullptr;
    if (C->isTemplated() || C->getDescribedFunctionTemplate() || C->isDeleted() || C->isDefaulted() || C->isCopyConstructor() ||
        C->isDelegatingConstructor() || !plainStruct(Context.getRecordType(C->getParent())))
      return nullptr;
    if (!isa<CompoundStmt>(C->getBody()))
      return nullptr;
    std::set<const FieldDecl *> Given;
    for (const CXXCtorInitializer *Init : C->inits()) {
      // The interface bases of a final class over interfaces are built by the compiler, decision 0166.
      if (Init->isBaseInitializer() && !Init->isWritten())
        continue;
      // A vector field that the list does not name starts empty, decision 0187. Clang may list it as an implicit initializer.
      if (!Init->isWritten() && Init->isMemberInitializer() && !Init->getMember()->hasInClassInitializer() && !localVec(Init->getMember()->getType()).isNull())
        continue;
      // A `std::array` field starts as zeros, from `f()`, `f{}` or a default member initializer `{}`. Any other start has no rule, decision 0196.
      if (Init->isMemberInitializer() && !fieldArray(Init->getMember()->getType()).isNull()) {
        if (!arrayZeros(Init->getInit()))
          return nullptr;
        if (!Init->isWritten()) {
          Given.insert(Init->getMember());
          continue;
        }
      }
      if (!Init->isWritten() || !Init->isMemberInitializer() || !Given.insert(Init->getMember()).second || readsObject(Init->getInit()))
        return nullptr;
    }
    for (const FieldDecl *F : C->getParent()->fields())
      if (!Given.count(F) && (F->hasInClassInitializer() || localVec(F->getType()).isNull()))
        return nullptr;
    return C;
  }

  // Whether a constructor that would be a value constructor leaves a `std::array` field with no start value, decision 0196. C++ leaves the elements without a value.
  bool arrayNoStart(const FunctionDecl *FD) const {
    const FunctionDecl *Def = nullptr;
    if (!isa<CXXConstructorDecl>(FD) || !FD->hasBody(Def))
      return false;
    const auto *C = cast<CXXConstructorDecl>(Def);
    if (C->isTemplated() || C->isDeleted() || C->isDefaulted() || C->isCopyConstructor() || C->isMoveConstructor() || C->isDelegatingConstructor() ||
        !plainStruct(Context.getRecordType(C->getParent())))
      return false;
    for (const CXXCtorInitializer *Init : C->inits())
      if (Init->isMemberInitializer() && !Init->isWritten() && !Init->getMember()->hasInClassInitializer() && !fieldArray(Init->getMember()->getType()).isNull() && !arrayZeros(Init->getInit()))
        return true;
    return false;
  }

  // The body of a value constructor: it returns the struct, built from the values of its init list in the order of the fields.
  // A constructor with a body first computes each value of the init list into a fresh local, as C++ runs the list first. Then come the statements of the
  // body, and the struct is built from the fresh locals, decision 0179. The name of a fresh local has a `'`, which no C++ name has.
  llvm::json::Array constructorBody(const CXXConstructorDecl *C) const {
    const unsigned At = line(C->getLocation());
    const auto *Body = cast<CompoundStmt>(C->getBody());
    llvm::json::Array Out, Args;
    // The list runs in the order of the fields. So when one field goes through a fresh local, every field does, decision 0187.
    std::vector<llvm::json::Value> Values;
    bool Locals = !Body->body_empty();
    // A `std::unique_ptr` field of `other` that the init list moves is null right after the init of the field that moves it, decisions 0197 and 0198.
    // `Nulled` holds the moved fields, and `After` holds, for each field of the struct in order, the moved field that is null after its init.
    std::vector<const FieldDecl *> Nulled;
    std::vector<const FieldDecl *> After;
    const ParmVarDecl *Other = C->getNumParams() == 1 ? C->getParamDecl(0) : nullptr;
    const auto readOther = [&](const FieldDecl *From) {
      return tag("Field", llvm::json::Array{tag("Var", llvm::json::Array{nameOf(Other), varType(Other)}), From->getNameAsString()});
    };
    for (const FieldDecl *F : C->getParent()->fields()) {
      // `f(n, x)` of a vector field is a vector of copies, and a vector field that the list does not name is empty, decision 0187.
      llvm::json::Value Value = nullptr;
      bool Seq = false;
      const FieldDecl *Moved = nullptr;
      // A move constructor `= default` moves each `std::unique_ptr` field and copies each scalar field, decision 0197.
      if (C->isDefaulted()) {
        Value = readOther(F);
        if (!ownVecElement(F->getType()).isNull()) {
          Nulled.push_back(F);
          Moved = F;
        }
      }
      for (const CXXCtorInitializer *Init : C->isDefaulted() ? ArrayRef<CXXCtorInitializer *>() : ArrayRef<CXXCtorInitializer *>(C->init_begin(), C->getNumCtorInitializers()))
        if (Init->getMember() == F && Init->isWritten()) {
          if (const FieldDecl *From = movedFrom(Init->getInit(), F, C); From && std::find(Nulled.begin(), Nulled.end(), From) == Nulled.end()) {
            Nulled.push_back(From);
            Moved = From;
            Value = readOther(From);
            continue;
          }
          Value = vecFill(Init->getInit(), At);
          // `f(std::move(v))` of a vector field and a local vector or a vector parameter by value `v` is the start value `Move(v)`, decision 0194.
          if (Value.getAsNull())
            if (const auto *Construct = dyn_cast<CXXConstructExpr>(Init->getInit()->IgnoreParenImpCasts());
                Construct && Construct->getNumArgs() == 1 && Construct->getConstructor()->isMoveConstructor() && !localVec(F->getType()).isNull())
              Value = vecMoveOf(Construct->getArg(0), localVec(F->getType()));
          Seq = !Value.getAsNull();
          if (!Seq)
            Value = expr(Init->getInit(), At);
        }
      // `f()` and `f{}` of a `std::array` field, and its default member initializer `{}`, are N zeros, decision 0196.
      if (const QualType Element = fieldArray(F->getType()); !Element.isNull())
        for (const CXXCtorInitializer *Init : C->inits())
          if (Init->getMember() == F && arrayZeros(Init->getInit())) {
            Value = tag("Fill", llvm::json::Array{tag("Lit", llvm::json::Array{seqExtent(F->getType()), type(Context.getSizeType())}),
                                                  tag("Lit", llvm::json::Array{number(0), type(Element)})});
            Seq = true;
          }
      if (Value.getAsNull()) {
        Value = "EmptyVec";
        Seq = true;
      }
      // The core reads `Fill`, `EmptyVec` and `Move` as the start of a local only. A moved field is null right after the init that moves it, decision 0198.
      Locals = Locals || Seq || !Nulled.empty();
      Values.push_back(std::move(Value));
      After.push_back(Moved);
    }
    size_t Next = 0;
    for (const FieldDecl *F : C->getParent()->fields()) {
      llvm::json::Value Value = std::move(Values[Next++]);
      const FieldDecl *Moved = After[Next - 1];
      if (!Locals) {
        Args.push_back(std::move(Value));
        continue;
      }
      const std::string Fresh = "'init'" + F->getNameAsString();
      // A local vector is a `Vec`, as in `varType`.
      const QualType Element = localVec(F->getType());
      llvm::json::Value Kind = Element.isNull() ? type(F->getType(), true) : tag("Vec", elementType(Element));
      Out.push_back(tag("Local", llvm::json::Array{Fresh, Kind, std::move(Value), number(At)}));
      Args.push_back(tag("Var", llvm::json::Array{Fresh, std::move(Kind)}));
      if (Moved)
        Out.push_back(tag("SetRefField", llvm::json::Array{nameOf(Other), Moved->getNameAsString(), "Nullopt", number(At)}));
    }
    if (!Body->body_empty()) {
      InConstructorBody = true;
      for (llvm::json::Value &One : stmts(Body))
        Out.push_back(std::move(One));
      InConstructorBody = false;
    }
    Out.push_back(tag("Return", llvm::json::Array{tag("Construct", llvm::json::Array{structKey(C->getParent()), std::move(Args)}), number(At)}));
    return Out;
  }

public:
  // A destructor that the class declares and the file defines `= default` out of line, `Box::~Box() = default;`. It is a destructor with an empty body, and its contract
  // stands on the declaration in the class, decision 0197. A destructor `= default` in the class is none, decision 0179.
  static bool outOfLineDefault(const FunctionDecl *FD) {
    return isa<CXXDestructorDecl>(FD) && FD->isDefaulted() && !FD->isImplicit() && FD->isOutOfLine() && FD->isThisDeclarationADefinition();
  }
  // A class template with type parameters only has instances that are structs of the model, decision 0188. Any other class template is refused.
  static bool typeOnlyClass(const ClassTemplateDecl *T) {
    if (!T)
      return false;
    for (const NamedDecl *P : *T->getTemplateParameters())
      if (!isa<TemplateTypeParmDecl>(P) || cast<TemplateTypeParmDecl>(P)->isParameterPack())
        return false;
    return true;
  }
  // An instance of a class template of the main file with type parameters only, as the compiler makes it, or null, decision 0188. An explicit
  // or a partial specialization is a class of its own, and the gate refuses it.
  const ClassTemplateSpecializationDecl *classInstance(const CXXRecordDecl *RD) const {
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(RD);
    if (!Spec || Spec->isDependentContext() || Spec->getSpecializationKind() == TSK_ExplicitSpecialization ||
        !Spec->getSpecializedTemplateOrPartial().is<ClassTemplateDecl *>())
      return nullptr;
    const ClassTemplateDecl *T = Spec->getSpecializedTemplate();
    return typeOnlyClass(T) && SM.isInMainFile(T->getLocation()) ? Spec : nullptr;
  }
  // A class template of the main file with type parameters only, and no instance, decision 0188. An instance has a definition, or it is refused
  // for its type arguments. A specialization that the file writes, and one that only a declaration names, are no instance.
  bool noInstanceClass(const CXXRecordDecl *RD) const {
    const ClassTemplateDecl *T = RD->getDescribedClassTemplate();
    if (!T || !typeOnlyClass(T) || !SM.isInMainFile(T->getLocation()))
      return false;
    for (const ClassTemplateSpecializationDecl *Spec : const_cast<ClassTemplateDecl *>(T)->specializations())
      if (Spec->getSpecializationKind() != TSK_ExplicitSpecialization && (Spec->hasDefinition() || !namedInstance(Spec)))
        return false;
    return true;
  }
  // An instance with no definition and a type argument that has no Dafny name is refused at its class, decision 0188.
  void refuseUnnamedInstances(const CXXRecordDecl *RD) const {
    const ClassTemplateDecl *T = RD->getDescribedClassTemplate();
    if (!T || !typeOnlyClass(T) || !SM.isInMainFile(T->getLocation()))
      return;
    for (const ClassTemplateSpecializationDecl *Spec : const_cast<ClassTemplateDecl *>(T)->specializations())
      if (Spec->getSpecializationKind() != TSK_ExplicitSpecialization && !namedInstance(Spec))
        unnamedEntry(Spec);
  }
  // Whether an instance of the class template made the member function of the pattern `FD`, decision 0188.
  bool memberHasInstance(const FunctionDecl *FD) const {
    const FunctionDecl *Pattern = FD->getCanonicalDecl();
    const ClassTemplateDecl *T = cast<CXXMethodDecl>(FD)->getParent()->getDescribedClassTemplate();
    for (const ClassTemplateSpecializationDecl *Spec : const_cast<ClassTemplateDecl *>(T)->specializations())
      for (const Decl *D : Spec->decls())
        if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && M->isDefined())
          if (const FunctionDecl *From = M->getInstantiatedFromMemberFunction(); From && From->getCanonicalDecl() == Pattern)
            return true;
    return false;
  }
  // The member function of a class template that the model reads at each instance, not at the template, decision 0188.
  bool inClassTemplate(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (!M || !M->isTemplated() || FD->getDescribedFunctionTemplate())
      return false;
    const ClassTemplateDecl *T = M->getParent()->getDescribedClassTemplate();
    return T && typeOnlyClass(T) && SM.isInMainFile(T->getLocation());
  }
  // A member function of an instance that the compiler made: not a member template, and one of a class that the model can read, decision 0188.
  bool instanceMember(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    return M && FD->isTemplateInstantiation() && !FD->getPrimaryTemplate() && classInstance(M->getParent());
  }
  // The place of a struct for the shell: an instance sits at the class template, decision 0188.
  SourceLocation structLoc(const CXXRecordDecl *RD) const {
    const ClassTemplateSpecializationDecl *Spec = classInstance(RD);
    return SM.getFileLoc(Spec ? Spec->getSpecializedTemplate()->getTemplatedDecl()->getLocation() : RD->getLocation());
  }
  // The refusal of a form with no instance: a function with no signature, whose result type is `Other` of the sentence, decision 0188.
  llvm::json::Value noInstanceEntry(StringRef Name, const std::string &Key, SourceLocation At, const char *Sentence) const {
    const SourceLocation Loc = SM.getFileLoc(At);
    return llvm::json::Object{{"name", Name}, {"key", Key}, {"file", file(Loc)}, {"line", number(line(Loc))},
                              {"params", llvm::json::Array{}}, {"ret", tag("Other", Sentence)}, {"trusted", nullptr},
                              {"interface", false}, {"hidden", llvm::json::Array{}}, {"conds", llvm::json::Array{}},
                              {"body", llvm::json::Array{tag("Unknown", llvm::json::Array{Sentence, number(line(Loc))})}}};
  }
  // An instance of a class template is a struct of the model when its type arguments are scalars, structs or enums, which have a Dafny name, decision 0188.
  bool namedInstance(const CXXRecordDecl *RD) const {
    const ClassTemplateSpecializationDecl *Spec = classInstance(RD);
    if (!Spec)
      return false;
    for (const TemplateArgument &A : Spec->getTemplateArgs().asArray()) {
      if (A.getKind() != TemplateArgument::Type)
        return false;
      const llvm::json::Value V = type(A.getAsType());
      const llvm::json::Object *O = V.getAsObject();
      if (!V.getAsString() && !(O && (O->get("Struct") || O->get("Enum"))))
        return false;
    }
    return true;
  }
  // The struct of an instance whose type arguments have no Dafny name is written with no field. The shell refuses it at the class, decision 0188.
  void unnamedEntry(const ClassTemplateSpecializationDecl *Spec) const {
    const std::string Key = structKey(Spec);
    if (Structs.count(Key))
      return;
    llvm::json::Array Of;
    for (const TemplateArgument &A : Spec->getTemplateArgs().asArray())
      Of.push_back(type(A.getAsType()));
    const SourceLocation Loc = structLoc(Spec);
    Structs.emplace(Key, llvm::json::Object{{"struct", Key}, {"name", Spec->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                            {"fields", llvm::json::Array{}}, {"members", llvm::json::Array{}}, {"of", std::move(Of)}});
  }

  // An interface, decision 0165: a class in the file with no field and no base, whose members are pure virtual `const` functions and a destructor that is
  // defaulted.
  bool isInterface(const CXXRecordDecl *RD) const {
    if (!RD || !RD->hasDefinition())
      return false;
    RD = RD->getDefinition();
    if (SM.isInSystemHeader(RD->getLocation()) || RD->isUnion() || RD->isLambda() || !RD->getIdentifier() || RD->isDependentContext() || isa<ClassTemplateSpecializationDecl>(RD) ||
        RD->getNumBases() || !RD->isPolymorphic() || !RD->field_empty())
      return false;
    bool Virtual = false;
    for (const Decl *D : RD->decls()) {
      if (D->isImplicit() || isa<AccessSpecDecl>(D))
        continue;
      const auto *M = dyn_cast<CXXMethodDecl>(D);
      if (!M)
        return false;
      if (isa<CXXDestructorDecl>(M)) {
        if (!M->isDefaulted())
          return false;
        continue;
      }
      if (isa<CXXConstructorDecl>(M) || M->isStatic() || !M->isVirtual() || !M->isPureVirtual() || M->isVolatile() || M->getRefQualifier() != RQ_None ||
          M->isOverloadedOperator() || isa<CXXConversionDecl>(M))
        return false;
      Virtual = true;
    }
    return Virtual;
  }
  // The interfaces that a class derives from, or none when it has a base that is no interface, a virtual base or a base that is not public, decision 0165.
  std::vector<const CXXRecordDecl *> interfaceBases(const CXXRecordDecl *RD) const {
    std::vector<const CXXRecordDecl *> Out;
    if (!RD || !RD->hasDefinition() || RD->getNumBases() == 0 || RD->getNumVBases() != 0)
      return Out;
    for (const CXXBaseSpecifier &Base : RD->getDefinition()->bases()) {
      const CXXRecordDecl *B = Base.getType()->getAsCXXRecordDecl();
      if (Base.isVirtual() || Base.getAccessSpecifier() != AS_public || !isInterface(B))
        return {};
      Out.push_back(B->getDefinition());
    }
    return Out;
  }
  // A final class whose bases are all interfaces, decision 0165.
  bool finalOverInterface(const CXXRecordDecl *RD) const {
    return RD && RD->hasDefinition() && RD->getDefinition()->isEffectivelyFinal() && !interfaceBases(RD).empty();
  }
  // A pure virtual function of an interface, decisions 0165 and 0169. One that is not `const` writes its object.
  bool ifaceMethod(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    return M && M->isPureVirtual() && isInterface(M->getParent());
  }
  // A member function, a constructor or a destructor that the model leaves out with no refusal, decision 0165: the defaulted destructor of an interface, and
  // each member of a class over an interface that is not final. A call on such a class may run an override of a subclass, so the model never reads its body.
  bool leftOut(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (!M)
      return false;
    const CXXRecordDecl *Parent = M->getParent();
    if (isa<CXXDestructorDecl>(M) && isInterface(Parent))
      return true;
    return !interfaceBases(Parent).empty() && !finalOverInterface(Parent);
  }
  // Writes the entry of an interface in the table of structs: no field, and the member table of its virtual functions, decision 0165.
  void interfaceEntry(const CXXRecordDecl *RD) const {
    RD = RD->getDefinition();
    const std::string Key = structKey(RD);
    if (Structs.count(Key))
      return;
    Structs.emplace(Key, nullptr);
    // The members are in the order of the declarations, decision 0166: a contract reads only the functions above it.
    std::vector<std::pair<std::string, std::vector<std::string>>> Named;
    for (const Decl *D : RD->decls())
      if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && ifaceMethod(M)) {
        const std::string Name = M->getNameAsString();
        auto At = std::find_if(Named.begin(), Named.end(), [&](const auto &N) { return N.first == Name; });
        if (At == Named.end())
          At = Named.insert(Named.end(), {Name, {}});
        At->second.push_back(this->key(M));
      }
    llvm::json::Array Members;
    for (const auto &[Name, Keys] : Named)
      if (Keys.size() == 1)
        Members.push_back(llvm::json::Array{Name, Keys.front()});
    const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
    Structs.at(Key) = llvm::json::Object{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                             {"fields", llvm::json::Array{}}, {"members", std::move(Members)}, {"interface", true},
                                             {"qualified", RD->getQualifiedNameAsString()}};
  }
  // The keys of the interfaces of a class, and the entry of each, for the table of structs, decision 0165.
  llvm::json::Array baseKeys(const CXXRecordDecl *RD) const {
    llvm::json::Array Out;
    for (const CXXRecordDecl *B : interfaceBases(RD)) {
      interfaceEntry(B);
      Out.push_back(structKey(B));
    }
    return Out;
  }
  // The entry of a class over an interface in the table of structs. A final class is a struct of 0073. One that is not final has an entry for its line only,
  // and no member, decision 0165.
  void classEntry(const CXXRecordDecl *RD) const {
    if (interfaceBases(RD).empty())
      return;
    if (finalOverInterface(RD)) {
      type(Context.getRecordType(RD));
      return;
    }
    const std::string Key = structKey(RD);
    if (Structs.count(Key))
      return;
    Structs.emplace(Key, nullptr);
    llvm::json::Array Bases = baseKeys(RD);
    const SourceLocation Loc = SM.getFileLoc(RD->getLocation());
    Structs.at(Key) = llvm::json::Object{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                             {"fields", llvm::json::Array{}}, {"members", llvm::json::Array{}}, {"bases", std::move(Bases)}, {"final", false}};
  }

  // A struct with a field of a struct with a destructor is written, also when no type names it, so the core refuses the field at its line, decision 0178.
  void holderEntry(const CXXRecordDecl *RD) const {
    if (!plainStruct(Context.getRecordType(RD)))
      return;
    for (const FieldDecl *F : RD->fields())
      if (const CXXRecordDecl *Held = plainStruct(F->getType()); Held && Held->hasUserDeclaredDestructor()) {
        type(Context.getRecordType(RD));
        return;
      }
  }

  // The struct of a class with a static member function that has a contract is written, also when no type names it, decision 0174.
  void staticEntry(const CXXRecordDecl *RD) const {
    if (!plainStruct(Context.getRecordType(RD)))
      return;
    for (const Decl *D : RD->decls())
      if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && listedStatic(M)) {
        type(Context.getRecordType(RD));
        return;
      }
  }

private:
  // A static member function of a plain struct, decision 0174: written as a free function with the name of its class. Null for any other function.
  const CXXMethodDecl *staticMember(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (!M || !M->isStatic() || M->isOverloadedOperator() || M->isTemplated() || M->getDescribedFunctionTemplate())
      return nullptr;
    return plainStruct(Context.getRecordType(M->getParent())) ? M : nullptr;
  }
  // A static member function that the struct lists as a member: one with a contract that the file defines or trusts, decision 0174.
  bool listedStatic(const FunctionDecl *FD) const {
    const CXXMethodDecl *M = staticMember(FD);
    if (!M)
      return false;
    const FunctionDecl *Def = M->getDefinition();
    return (Def || trustedReason(M)) && !contractOf(SM, Def ? Def : M).Lines.empty();
  }
  // A member function that is written as a function, decision 0089: not static, not virtual, no ref-qualifier, not an operator other
  // than `operator()`, decision 0098, a conversion, a constructor or a destructor, not a template, and a member of a plain struct. Null for any other function.
  // One that is not `const` writes its object, decision 0096.
  const CXXMethodDecl *member(const FunctionDecl *FD) const {
    const auto *M = dyn_cast<CXXMethodDecl>(FD);
    if (M && ifaceMethod(M))
      return M;
    if (!M || M->isStatic() || (M->isVirtual() && !finalOverInterface(M->getParent())) || M->isVolatile() || M->isExplicitObjectMemberFunction() || M->getRefQualifier() != RQ_None || (M->isOverloadedOperator() && M->getOverloadedOperator() != OO_Call) ||
        isa<CXXConversionDecl>(M) || isa<CXXConstructorDecl>(M) || (isa<CXXDestructorDecl>(M) && ((M->isDefaulted() && !outOfLineDefault(M)) || M->isDeleted() || M->isImplicit())) || M->isTemplated() || M->getDescribedFunctionTemplate())
      return nullptr;
    return plainStruct(Context.getRecordType(M->getParent())) ? M : nullptr;
  }
  // A member function that is `const`: pure, so a contract may call it, decision 0090.
  const CXXMethodDecl *constMember(const FunctionDecl *FD) const {
    const CXXMethodDecl *M = member(FD);
    return M && M->isConst() ? M : nullptr;
  }

  // The type of `this` in a member function of a plain struct, by the key of the struct. `ThisMut` when the function writes its object.
  llvm::json::Value thisType(const CXXRecordDecl *Parent, bool Writes = false) const {
    if (isInterface(Parent)) {
      interfaceEntry(Parent);
      return tag(Writes ? "IfaceMut" : "Iface", structKey(Parent->getDefinition()));
    }
    const CXXRecordDecl *RD = plainStruct(Context.getRecordType(Parent));
    type(Context.getRecordType(Parent));  // writes the struct
    return tag(Writes ? "ThisMut" : "This", structKey(RD));
  }

  // The key of a struct, as the key of a function that has no mangled name: the qualified name, `@` and the place of the definition.
public:
  // An instance of a class template has its type arguments in the name and the place of its class template, decision 0188.
  std::string structKey(const CXXRecordDecl *RD) const {
    const SourceLocation Loc = structLoc(RD);
    std::string Name = RD->getQualifiedNameAsString();
    if (classInstance(RD)) {
      Name.clear();
      llvm::raw_string_ostream OS(Name);
      RD->getNameForDiagnostic(OS, Context.getPrintingPolicy(), true);
    }
    return Name + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }

private:
  // The enum class of the file that a type is, decision 0109, or null: a definition in a user file, scoped, with an enumerator and no value
  // written for any. A qualified type is none, as for `scalar`.
  const EnumDecl *plainEnum(QualType T) const {
    // A const value is the same value. Any other qualifier is none, as for `scalar`.
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    if (Canon.hasQualifiers())
      return nullptr;
    const auto *Type = dyn_cast<EnumType>(Canon.getTypePtr());
    const EnumDecl *ED = Type ? Type->getDecl()->getDefinition() : nullptr;
    if (!ED || !ED->isScoped() || SM.isInSystemHeader(ED->getLocation()) || ED->enumerators().empty())
      return nullptr;
    for (const EnumConstantDecl *E : ED->enumerators())
      if (E->getInitExpr())
        return nullptr;
    return ED;
  }
  // The place of an enumerator among those of its enum, decision 0109.
  static unsigned enumeratorPlace(const EnumDecl *ED, const EnumConstantDecl *Enumerator) {
    unsigned Place = 0;
    for (const EnumConstantDecl *E : ED->enumerators()) {
      if (E == Enumerator)
        break;
      ++Place;
    }
    return Place;
  }
  // The key of an enum, as the key of a struct.
  std::string enumKey(const EnumDecl *ED) const {
    const SourceLocation Loc = SM.getFileLoc(ED->getLocation());
    return ED->getQualifiedNameAsString() + "@" + file(Loc) + ":" + std::to_string(line(Loc)) + ":" + std::to_string(SM.getExpansionColumnNumber(Loc));
  }
  // The enum as a type, written once with its enumerators in order.
  llvm::json::Value enumType(const EnumDecl *ED) const {
    const std::string Key = enumKey(ED);
    if (!Structs.count(Key)) {
      llvm::json::Array Names;
      for (const EnumConstantDecl *E : ED->enumerators())
        Names.push_back(E->getNameAsString());
      const SourceLocation Loc = SM.getFileLoc(ED->getLocation());
      Structs.emplace(Key, llvm::json::Object{{"enum", Key}, {"name", ED->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))}, {"enumerators", std::move(Names)}});
    }
    return tag("Enum", Key);
  }

  // The enum class of the file that is its underlying integer, decision 0175, or null: a definition in a user file, scoped, with a fixed
  // underlying type of the subset other than bool, a value written for an enumerator, and no negative value. A qualified type is none, as for `plainEnum`.
  const EnumDecl *valuedEnum(QualType T) const {
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    if (Canon.hasQualifiers())
      return nullptr;
    const auto *Type = dyn_cast<EnumType>(Canon.getTypePtr());
    const EnumDecl *ED = Type ? Type->getDecl()->getDefinition() : nullptr;
    if (!ED || !ED->isScoped() || !ED->isFixed() || SM.isInSystemHeader(ED->getLocation()) || ED->enumerators().empty())
      return nullptr;
    const char *Under = scalar(ED->getIntegerType()) ? scalar(ED->getIntegerType()) : smallScalar(ED->getIntegerType());
    if (!Under || StringRef(Under) == "Bool")
      return nullptr;
    bool Written = false;
    for (const EnumConstantDecl *E : ED->enumerators()) {
      if (E->getInitVal().isNegative())
        return nullptr;
      Written |= E->getInitExpr() != nullptr;
    }
    return Written ? ED : nullptr;
  }
  // The valued enum as a type: its underlying integer. The line with its enumerators and their values is written once, for the contracts.
  llvm::json::Value valuedType(const EnumDecl *ED) const {
    const std::string Key = enumKey(ED);
    if (!Structs.count(Key)) {
      llvm::json::Array Values;
      for (const EnumConstantDecl *E : ED->enumerators())
        Values.push_back(llvm::json::Array{E->getNameAsString(), number(E->getInitVal().getZExtValue())});
      Structs.emplace(Key, llvm::json::Object{{"valued", ED->getNameAsString()}, {"values", std::move(Values)}});
    }
    return scalar(ED->getIntegerType()) ? llvm::json::Value(scalar(ED->getIntegerType())) : llvm::json::Value(smallScalar(ED->getIntegerType()));
  }
  // `std::chrono::milliseconds`, decision 0175: `std::chrono::duration<int64_t, std::milli>`. Any other duration is none.
  bool isMillis(QualType T) const {
    QualType Canon = T.getCanonicalType();
    Canon.removeLocalConst();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Canon.hasQualifiers() ? nullptr : Canon->getAsCXXRecordDecl());
    if (!Spec || Spec->getQualifiedNameAsString() != "std::chrono::duration" || Spec->getTemplateArgs().size() != 2 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type || Spec->getTemplateArgs()[1].getKind() != TemplateArgument::Type)
      return false;
    const auto *Ratio = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Spec->getTemplateArgs()[1].getAsType()->getAsCXXRecordDecl());
    if (!Ratio || Ratio->getName() != "ratio" || Ratio->getTemplateArgs().size() != 2 || Ratio->getTemplateArgs()[0].getKind() != TemplateArgument::Integral ||
        Ratio->getTemplateArgs()[1].getKind() != TemplateArgument::Integral)
      return false;
    const char *Rep = scalar(Spec->getTemplateArgs()[0].getAsType());
    return Rep && StringRef(Rep) == "I64" && Ratio->getTemplateArgs()[0].getAsIntegral() == 1 && Ratio->getTemplateArgs()[1].getAsIntegral() == 1000;
  }
  // A `std::array`, by value or by reference, with no qualifier looked at.
  static bool isStdArray(QualType T) {
    if (T->isReferenceType())
      T = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
    return Spec && Spec->isInStdNamespace() && Spec->getName() == "array";
  }

  // A parameter of type `T&` for a scalar or a struct of the file is `Mut(T)`, decision 0108, else null. A const reference is a value, and any other
  // reference stays `Other`.
  // A parameter `T&&` of a plain struct is the same, decision 0179. A `T&&` of anything else stays `Other`.
  llvm::json::Value mutRef(QualType T) const {
    if (!T->isReferenceType())
      return nullptr;
    const QualType Pointee = T->getPointeeType();
    if (Pointee.getCanonicalType().hasQualifiers())
      return nullptr;
    if (!T->isLValueReferenceType())
      return plainStruct(Pointee) ? tag("Mut", type(Pointee)) : llvm::json::Value(nullptr);
    if (const char *S = scalar(Pointee))
      return tag("Mut", S);
    if (plainStruct(Pointee))
      return tag("Mut", type(Pointee));
    // A reference of an interface, which a virtual function that writes may run on, decision 0169.
    if (const CXXRecordDecl *RD = Pointee->getAsCXXRecordDecl(); RD && isInterface(RD)) {
      interfaceEntry(RD);
      return tag("Mut", tag("Struct", structKey(RD->getDefinition())));
    }
    return nullptr;
  }
  // The operators that a free function may overload as a function of the model, decision 0175.
  static bool freeOperator(OverloadedOperatorKind Kind) {
    switch (Kind) {
    case OO_Plus: case OO_Minus: case OO_Star: case OO_Slash: case OO_Percent: case OO_Amp: case OO_Pipe:
    case OO_EqualEqual: case OO_ExclaimEqual: case OO_Less: case OO_LessEqual: case OO_Greater: case OO_GreaterEqual:
      return true;
    default:
      return false;
    }
  }
  // The element of a pointer to const, decisions 0140 and 0141, or null: `const T*` for a scalar or a plain struct, with no other qualifier.
  QualType constPointee(QualType T) const {
    const QualType Canon = T.getCanonicalType();
    if (!Canon->isPointerType() || Canon.hasQualifiers())
      return QualType();
    QualType Pointee = Canon->getPointeeType();
    if (!Pointee.isConstQualified())
      return QualType();
    Pointee.removeLocalConst();
    return !Pointee.hasQualifiers() && (scalar(Pointee) || plainStruct(Pointee)) ? Pointee : QualType();
  }
  // The element of a vector by reference that the function writes, decision 0145, or null: `std::vector<T>&` with no const, for a scalar `T` other
  // than bool, or a plain struct, decision 0163. A vector of bool stays `Other`.
  // A parameter `std::vector<T>&&` is the same, decision 0185.
  QualType mutSeq(QualType T) const {
    if (!T->isReferenceType())
      return QualType();
    const QualType Vector = T->getPointeeType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Vector->getAsCXXRecordDecl());
    if (Vector.getCanonicalType().hasQualifiers() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "vector" || Spec->getTemplateArgs().size() == 0 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    return vectorElement(Spec->getTemplateArgs()[0].getAsType());
  }
  // The element of a vector that the function owns or writes: a scalar other than bool, or a plain struct, with no qualifier, or null.
  QualType vectorElement(QualType Elem, bool Owns = true) const {
    if (Elem.getCanonicalType().hasQualifiers())
      return QualType();
    if (Owns && !ownVecElement(Elem).isNull())
      return Elem;
    const char *S = scalar(Elem);
    return (S ? StringRef(S) != "Bool" : plainStruct(Elem) != nullptr) ? Elem : QualType();
  }
  // The element of a local `std::vector<T>` by value, which the function owns, decision 0160, or null: no reference, and a scalar `T` other than bool.
  // A `const` on the vector is looked through. A span is a view, not a vector, so it is none.
  QualType localVec(QualType T, bool Owns = true) const {
    if (T->isReferenceType())
      return QualType();
    const QualType Vector = T.getUnqualifiedType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Vector->getAsCXXRecordDecl());
    if (T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "vector" || Spec->getTemplateArgs().size() == 0 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    return vectorElement(Spec->getTemplateArgs()[0].getAsType(), Owns);
  }
  // The element of a local `std::array<T, N>` by value, decision 0184, or null: no reference, and an element as for a local vector.
  QualType localArray(QualType T) const {
    if (T->isReferenceType())
      return QualType();
    const auto *Spec = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T.getUnqualifiedType()->getAsCXXRecordDecl());
    if (T.isVolatileQualified() || !Spec || !Spec->isInStdNamespace() || Spec->getName() != "array" || Spec->getTemplateArgs().size() == 0 ||
        Spec->getTemplateArgs()[0].getKind() != TemplateArgument::Type)
      return QualType();
    return vectorElement(Spec->getTemplateArgs()[0].getAsType());
  }
  // The element of a parameter `std::vector<T>` by value, with no qualifier, decision 0194, or null.
  QualType paramVec(QualType T) const { return T.hasQualifiers() ? QualType() : localVec(T); }
  // Whether an expression names a vector that the function writes: a vector by reference, decision 0145, a vector parameter by value, decision 0194,
  // or a local vector, decision 0160.
  bool isMutSeq(const Expr *E) const {
    const auto *Ref = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts());
    if (!Ref)
      return false;
    if (isa<ParmVarDecl>(Ref->getDecl()))
      return !mutSeq(Ref->getDecl()->getType()).isNull() || !paramVec(Ref->getDecl()->getType()).isNull();
    const auto *Var = dyn_cast<VarDecl>(Ref->getDecl());
    return Var && Var->hasLocalStorage() && (!localVec(Var->getType()).isNull() || !localArray(Var->getType()).isNull());
  }
  // The element of a vector that a name holds and the function can write: a vector parameter by reference, a vector parameter by value, decision 0194, or a local vector, decision 0185. Else null.
  QualType sourceVec(const ValueDecl *D) const {
    if (isa<ParmVarDecl>(D))
      return mutSeq(D->getType()).isNull() ? paramVec(D->getType()) : mutSeq(D->getType());
    const auto *Var = dyn_cast<VarDecl>(D);
    return Var && Var->hasLocalStorage() ? localVec(Var->getType()) : QualType();
  }
  // `std::move(v)` of a local vector or of a vector parameter by value `v`, of the element `Element`, as `Move(v, type)`, decision 0194. Null for any other form.
  llvm::json::Value vecMoveOf(const Expr *E, QualType Element) const {
    const auto *Move = dyn_cast<CallExpr>(E->IgnoreParenImpCasts());
    if (!Move || Move->getNumArgs() != 1 || !Move->getDirectCallee() || !Move->getDirectCallee()->isInStdNamespace() || !Move->getDirectCallee()->getDeclName().isIdentifier() ||
        Move->getDirectCallee()->getName() != "move")
      return nullptr;
    const auto *Ref = dyn_cast<DeclRefExpr>(Move->getArg(0)->IgnoreParenImpCasts());
    const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
    if (!Var || !(isa<ParmVarDecl>(Var) ? !paramVec(Var->getType()).isNull() : Var->hasLocalStorage()) || !sameElement(sourceVec(Var), Element))
      return nullptr;
    return tag("Move", llvm::json::Array{Var->getNameAsString(), tag("Vec", elementType(Element))});
  }
  // `std::move(v)` of a vector `v` that the function writes, as the start value of the local `Var`, of the same element: `Move(v, type)`, decision 0185. The core reads
  // the value of `v` as the body leaves it, then `v` with any value. Any other place of a move of a vector keeps its refusal. Null for any other form.
  llvm::json::Value vecMove(const Expr *Init, QualType Target) const {
    const auto *Construct = dyn_cast<CXXConstructExpr>(Init->IgnoreParenImpCasts());
    if (!Construct || Construct->getNumArgs() != 1 || !Construct->getConstructor()->isMoveConstructor() || localVec(Target).isNull())
      return nullptr;
    const auto *Move = dyn_cast<CallExpr>(Construct->getArg(0)->IgnoreParenImpCasts());
    if (!Move || Move->getNumArgs() != 1 || !Move->getDirectCallee() || !Move->getDirectCallee()->isInStdNamespace() || !Move->getDirectCallee()->getDeclName().isIdentifier() ||
        Move->getDirectCallee()->getName() != "move")
      return nullptr;
    const auto *Ref = dyn_cast<DeclRefExpr>(Move->getArg(0)->IgnoreParenImpCasts());
    if (!Ref || !sameElement(sourceVec(Ref->getDecl()), localVec(Target)))
      return nullptr;
    return tag("Move", llvm::json::Array{Ref->getDecl()->getNameAsString(), tag("Seq", llvm::json::Array{elementType(localVec(Target)), nullptr})});
  }
  // `std::vector<T> v(n, x);` as the start value of a local is a vector of n copies of x: `Fill(n, x)`, decision 0185. The count is a size_t. Only the constructor
  // `(size_type, const value_type&, const allocator_type&)` with the allocator as its default, written with parentheses, is it: `v(3)` and `v{3, 0}` are not.
  // In any other place the construction keeps its refusal. Null for any other form.
  llvm::json::Value vecFill(const Expr *Init, unsigned Near) const {
    const auto *Construct = dyn_cast<CXXConstructExpr>(Init->IgnoreParenImpCasts());
    if (!Construct || Construct->getNumArgs() != 3 || Construct->isListInitialization() || localVec(Construct->getType()).isNull() ||
        Construct->getArg(0)->getType().getUnqualifiedType().getCanonicalType() != Context.getSizeType() || isa<CXXDefaultArgExpr>(Construct->getArg(1)) ||
        !isa<CXXDefaultArgExpr>(Construct->getArg(2)) || !Construct->getConstructor()->getParamDecl(1)->getType()->isLValueReferenceType() ||
        !sameElement(Construct->getConstructor()->getParamDecl(1)->getType()->getPointeeType(), localVec(Construct->getType())))
      return nullptr;
    // The value binds to `const T&`, so a temporary holds it. The temporary is not the value.
    const Expr *Value = Construct->getArg(1);
    if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(Value))
      Value = Held->getSubExpr();
    return tag("Fill", llvm::json::Array{expr(Construct->getArg(0), Near), expr(Value, Near)});
  }
  static bool sameElement(QualType A, QualType B) {
    return !A.isNull() && !B.isNull() && A.getCanonicalType().getUnqualifiedType() == B.getCanonicalType().getUnqualifiedType();
  }
  // The type of a parameter, or of a name that reads one. A pointer to const is a `Ptr` of what it points to, decisions 0140 and 0141.
  llvm::json::Value paramType(QualType T) const {
    llvm::json::Value Written = mutRef(T);
    if (!Written.getAsNull())
      return Written;
    if (const QualType Element = constPointee(T); !Element.isNull())
      return tag("Ptr", type(Element));
    if (const QualType Element = mutSeq(T); !Element.isNull())
      return tag("MutSeq", elementType(Element));
    // A vector by value is a copy that the function owns, decision 0194. The core makes it a local of the body.
    if (const QualType Element = paramVec(T); !Element.isNull())
      return tag("Vec", elementType(Element));
    // A `unique_ptr` parameter is read by const reference only, decision 0142. By value it has no rule: it moves.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified())
      if (const QualType Element = ownElement(T->getPointeeType()); !Element.isNull())
        return tag("Own", ownScalar(Element));
    // By value, a unique_ptr of a struct or an interface is a value that the function owns, decision 0171.
    if (!ownVecElement(T).isNull() && !T.isConstQualified())
      return tag("Own", ownScalar(ownElement(T)));
    if (isOwn(T))
      return tag("Other", T.getAsString(Context.getPrintingPolicy()));
    // A parameter `const B&` of an interface is a value of the interface, decision 0165. A pointer, a local, a result and a field have no rule.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified())
      if (const CXXRecordDecl *RD = T->getPointeeType()->getAsCXXRecordDecl(); RD && isInterface(RD)) {
        interfaceEntry(RD);
        return tag("IfaceRef", structKey(RD->getDefinition()));
      }
    // A parameter `const T&` of a scalar `T` is the scalar by value, decision 0175.
    if (T->isLValueReferenceType() && T->getPointeeType().isConstQualified()) {
      const QualType Pointee = T->getPointeeType().getUnqualifiedType();
      if (scalar(Pointee) || smallScalar(Pointee))
        return type(Pointee);
    }
    return type(T);
  }
  // The type of a result. A `std::vector<T>` by value with no qualifier is a `Vec`, decision 0163: the function gives a copy. A span stays `Other`.
  llvm::json::Value resultType(QualType T) const {
    if (!T.hasQualifiers())
      if (const QualType Element = localVec(T, false); !Element.isNull())
        return tag("Vec", type(Element));
    return type(T);
  }
  // A const member function that gives back `const T&` of a scalar or a plain struct `T`, whose body is one `return` of a field of the object, or `f[i]`,
  // `f.at(i)` or `f.back()` of a vector field, decision 0191. The model reads its result as the value `T`. Else null, and the reference keeps its refusal.
  // ponytail: the body is that one statement. Upgrade: any body whose every return has the form.
  QualType valueResult(const FunctionDecl *FD) const {
    const auto *M = dyn_cast_or_null<CXXMethodDecl>(FD);
    if (!M || !M->isConst() || M->isVirtual() || !member(M) || !M->getReturnType()->isLValueReferenceType() || !M->getReturnType()->getPointeeType().isConstQualified())
      return QualType();
    const QualType Pointee = M->getReturnType()->getPointeeType().getUnqualifiedType();
    if (!(scalar(Pointee) || smallScalar(Pointee) || plainStruct(Pointee)))
      return QualType();
    const FunctionDecl *Def = M->getDefinition();
    const auto *Body = Def ? dyn_cast_or_null<CompoundStmt>(Def->getBody()) : nullptr;
    const auto *Return = Body && Body->size() == 1 ? dyn_cast<ReturnStmt>(Body->body_front()) : nullptr;
    if (!Return || !Return->getRetValue())
      return QualType();
    // A returned temporary dies at the end of the return, so it is never the value, decision 0181. IgnoreParenImpCasts skips a MaterializeTemporaryExpr.
    if (holdsTemporary(Return->getRetValue()))
      return QualType();
    const Expr *Value = Return->getRetValue()->IgnoreParenImpCasts();
    if (Value->getType().getUnqualifiedType().getCanonicalType() != Pointee.getCanonicalType())
      return QualType();
    bool Form = objectField(Value) != nullptr;
    if (const auto *Element = dyn_cast<CXXOperatorCallExpr>(Value); Element && Element->getOperator() == OO_Subscript && Element->getNumArgs() == 2)
      Form = isFieldVec(Element->getArg(0));
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(Value); Call && Call->getMethodDecl() && Call->getMethodDecl()->getDeclName().isIdentifier() && Call->getImplicitObjectArgument()) {
      const StringRef Name = Call->getMethodDecl()->getName();
      Form = ((Name == "at" && Call->getNumArgs() == 1) || (Name == "back" && Call->getNumArgs() == 0)) && isFieldVec(Call->getImplicitObjectArgument());
    }
    return Form ? Pointee : QualType();
  }
  // The loop variable of a range-for has the element type whether it is `const` or a const reference, decision 0143. The loop is written only
  // when that type is the element's.
  llvm::json::Value varType(const ValueDecl *D) const {
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->isCXXForRangeDecl())
      return type(Var->getType().getNonReferenceType().getUnqualifiedType());
    // A local vector is a `Vec`, decision 0160.
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->hasLocalStorage() && !isa<ParmVarDecl>(Var))
      if (const QualType Element = localVec(Var->getType()); !Element.isNull())
        return tag("Vec", elementType(Element));
    // A `const` on a local changes no value of the model, decision 0166.
    if (const auto *Var = dyn_cast<VarDecl>(D); Var && Var->hasLocalStorage() && !isa<ParmVarDecl>(Var) && !Var->getType()->isReferenceType() && !Var->isCXXForRangeDecl() &&
                                                 Var->getType().isLocalConstQualified()) {
      QualType Plain = Var->getType();
      Plain.removeLocalConst();
      if (scalar(Plain) || smallScalar(Plain) || plainEnum(Plain) || valuedEnum(Plain) || isMillis(Plain))
        return type(Plain);
    }
    // The parameter of a lambda is the element, whether it is by value or by const reference, decision 0149.
    if (const auto *Param = dyn_cast<ParmVarDecl>(D); Param && isa<CXXMethodDecl>(Param->getDeclContext()) && cast<CXXMethodDecl>(Param->getDeclContext())->getParent()->isLambda())
      return type(Param->getType().getNonReferenceType().getUnqualifiedType());
    return isa<ParmVarDecl>(D) ? paramType(D->getType()) : type(D->getType());
  }

public:
  llvm::json::Value type(QualType T, bool Field = false) const {
    if (const char *S = scalar(T))
      return S;
    if (const char *S = smallScalar(T))
      return S;
    if (const EnumDecl *ED = plainEnum(T))
      return enumType(ED);
    if (const EnumDecl *ED = valuedEnum(T))
      return valuedType(ED);
    // A duration in milliseconds is its count, decision 0175.
    if (isMillis(T))
      return "I64";
    // A `double` by value is a real that only compares, decision 0150. A field, a sequence, an optional and a reference of it stay out.
    if (!Field && isDouble(T))
      return "F64";
    // Decision 0074: a struct is by value or by const lvalue reference. Any other reference stays `Other`.
    const bool Writable = T->isReferenceType() && !(T->isLValueReferenceType() && T->getPointeeType().isConstQualified());
    if (const CXXRecordDecl *RD = Writable ? nullptr : plainStruct(T)) {
      const std::string Key = structKey(RD);
      if (!Structs.count(Key)) {
        Structs.emplace(Key, nullptr);  // a recursive struct finds itself here, decision 0076
        llvm::json::Array Fields;
        for (const FieldDecl *F : RD->fields())
          Fields.push_back(llvm::json::Array{F->getNameAsString(), type(F->getType(), true)});
        // The member functions that are written as functions, as (name, key), decision 0090. A name that two of them share is left out:
        // a contract cannot tell the overloads apart, so it calls none.
        std::map<std::string, std::vector<std::string>> Named;
        for (const Decl *D : RD->decls())
          // An override that writes its object is a member too, so the check finds it. A contract cannot call it, decision 0169.
          if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && (constMember(M) || (M->isVirtual() && member(M)) || (isa<CXXDestructorDecl>(M) && member(M))))
            // A const member function that has no body here has no function of the model. Its key is its display name, which the core
            // prints in the sentence of a contract that calls it, decision 0188.
            Named[isa<CXXDestructorDecl>(M) ? "~" : M->getNameAsString()].push_back(
                constMember(M) && !M->isDefined() && !trustedReason(M) ? name(M) : key(M));
        // The static member functions with a contract, under their qualified names, decision 0174.
        for (const Decl *D : RD->decls())
          if (const auto *M = dyn_cast<CXXMethodDecl>(D); M && listedStatic(M))
            Named[name(M)].push_back(key(M));
        llvm::json::Array Members;
        for (const auto &[Name, Keys] : Named)
          if (Keys.size() == 1)
            Members.push_back(llvm::json::Array{Name, Keys.front()});
        const SourceLocation Loc = structLoc(RD);
        llvm::json::Object Entry{{"struct", Key}, {"name", RD->getNameAsString()}, {"file", file(Loc)}, {"line", number(line(Loc))},
                                 {"fields", std::move(Fields)}, {"members", std::move(Members)}};
        // An instance of a class template names its type arguments, and the shell makes `Box'of'int32` of them, decision 0188.
        if (const ClassTemplateSpecializationDecl *Spec = classInstance(RD)) {
          llvm::json::Array Of;
          for (const TemplateArgument &A : Spec->getTemplateArgs().asArray())
            Of.push_back(type(A.getAsType()));
          Entry["of"] = std::move(Of);
        }
        // A final class over interfaces names them, decision 0165.
        if (finalOverInterface(RD)) {
          Entry["bases"] = baseKeys(RD);
          Entry["final"] = true;
        }
        Structs.at(Key) = std::move(Entry);
      }
      return tag("Struct", Key);
    }
    if (const QualType E = seqElement(T, Field); !E.isNull())
      return tag("Seq", llvm::json::Array{elementType(E), seqExtent(T)});
    if (const QualType E = optType(T); !E.isNull())
      return tag("Opt", type(E));
    // A field holds a unique_ptr of a struct or an interface, decision 0171.
    if (const QualType E = Field ? (ownVecElement(T).isNull() ? QualType() : ownElement(T)) : ownElement(T); !E.isNull())
      return tag("Own", ownScalar(E));
    // An instance of a class template with a type argument that has no Dafny name is refused at its class, decision 0188.
    if (const ClassTemplateSpecializationDecl *Spec = classInstance(T.getNonReferenceType()->getAsCXXRecordDecl()); Spec && !namedInstance(Spec))
      unnamedEntry(Spec);
    return tag("Other", T.getAsString(Context.getPrintingPolicy()));
  }

private:
  // The statements of a branch or of the body: a compound statement is its list, and any other statement is a list of one.
  llvm::json::Array stmts(const Stmt *S) const {
    llvm::json::Array Out;
    if (const auto *Block = dyn_cast<CompoundStmt>(S))
      for (const Stmt *Child : Block->body())
        pushStmt(Child, Out);
    else
      pushStmt(S, Out);
    return Out;
  }

  // A statement with the lines above it, and before it the statements that a chain of calls in it needs, decision 0183.
  // A control statement takes none: its condition runs more than once, or not at all.
  void pushStmt(const Stmt *Child, llvm::json::Array &Out) const {
    bodyLines(Child, Out);
    const Stmt *SavedFor = HoistFor;
    llvm::json::Array Saved = std::move(Prelude);
    Prelude = llvm::json::Array();
    HoistFor = isa<IfStmt, WhileStmt, ForStmt, CXXForRangeStmt, SwitchStmt, CompoundStmt, DoStmt>(Child) ? nullptr : Child;
    llvm::json::Value One = stmt(Child);
    for (llvm::json::Value &Step : Prelude)
      Out.push_back(std::move(Step));
    Out.push_back(std::move(One));
    Prelude = std::move(Saved);
    HoistFor = SavedFor;
  }

  // Whether the function around a `return` gives a reference.
  bool returnsReference(const ReturnStmt *Return) const {
    DynTypedNode Node = DynTypedNode::create(*Return);
    for (;;) {
      const auto Parents = Context.getParents(Node);
      if (Parents.empty())
        return false;
      Node = Parents[0];
      if (const auto *FD = Node.get<FunctionDecl>())
        return FD->getReturnType()->isReferenceType();
    }
  }
  static bool holdsTemporary(const Stmt *S) {
    if (isa<MaterializeTemporaryExpr>(S))
      return true;
    for (const Stmt *Child : S->children())
      if (Child && holdsTemporary(Child))
        return true;
    return false;
  }

  // A member function that writes its object and returns it, decision 0183: not const, not virtual, a member of the model, and the result `T&` of its
  // own class. Whether each return is `return *this;` is `fluent`.
  const CXXMethodDecl *fluentSignature(const FunctionDecl *FD) const {
    const auto *M = dyn_cast_or_null<CXXMethodDecl>(FD);
    if (!M || M->isConst() || M->isVirtual() || !member(M))
      return nullptr;
    const QualType Result = M->getReturnType();
    if (!Result->isLValueReferenceType() || Result->getPointeeType().isConstQualified())
      return nullptr;
    return Result->getPointeeType().getCanonicalType().getUnqualifiedType() == Context.getRecordType(M->getParent()).getCanonicalType() ? M : nullptr;
  }
  static bool isReturnThis(const ReturnStmt *Return) {
    const Expr *Value = Return->getRetValue() ? Return->getRetValue()->IgnoreParenImpCasts() : nullptr;
    const auto *Deref = dyn_cast_or_null<UnaryOperator>(Value);
    return Deref && Deref->getOpcode() == UO_Deref && isa<CXXThisExpr>(Deref->getSubExpr()->IgnoreParenImpCasts());
  }
  // Whether each `return` of a body is `return *this;`. A lambda in the body has returns of its own.
  static bool returnsOnlyThis(const Stmt *S) {
    if (!S || isa<LambdaExpr>(S))
      return true;
    if (const auto *Return = dyn_cast<ReturnStmt>(S))
      return isReturnThis(Return);
    for (const Stmt *Child : S->children())
      if (!returnsOnlyThis(Child))
        return false;
    return true;
  }
  // A member function that gives back its object, whose body ends in `return *this;` and has no other return, decision 0183.
  bool fluent(const FunctionDecl *FD) const {
    const FunctionDecl *Def = FD ? FD->getDefinition() : nullptr;
    const auto *Body = Def ? dyn_cast_or_null<CompoundStmt>(Def->getBody()) : nullptr;
    const auto *Last = Body && !Body->body_empty() ? dyn_cast<ReturnStmt>(Body->body_back()) : nullptr;
    return fluentSignature(FD) && Last && isReturnThis(Last) && returnsOnlyThis(Body);
  }
  // A call of such a function.
  const CXXMemberCallExpr *fluentCall(const Expr *E) const {
    const auto *Call = E ? dyn_cast<CXXMemberCallExpr>(E->IgnoreParenImpCasts()) : nullptr;
    return Call && Call->getDirectCallee() && fluent(Call->getDirectCallee()) ? Call : nullptr;
  }
  // The call `Call` of a function that gives back its object, with the calls of its object as nested calls: the form of 0104 and 0177. The core takes it
  // where C++ runs it once, and refuses it elsewhere.
  llvm::json::Value nested(const CXXMemberCallExpr *Call, unsigned Near) const {
    const Expr *Object = Call->getImplicitObjectArgument()->IgnoreParenImpCasts();
    const auto *Callee = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
    if (!Callee || (Callee->isArrow() && !isa<CXXThisExpr>(Object)))
      return tag("Unknown", llvm::json::Array{"the result of a call that gives back its object, used as a value", number(Near)});
    const unsigned At = line(Call->getBeginLoc());
    const CXXMemberCallExpr *Inner = fluentCall(Object);
    llvm::json::Array Args{Inner ? nested(Inner, Near) : expr(Object, At)};
    for (unsigned I = 0; I < Call->getNumArgs(); ++I)
      Args.push_back(callArg(Call->getDirectCallee(), I, Call->getArg(I), At));
    return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(At)});
  }
  // A chain of calls that give back their object, `x.f(a).g(b)`, as the steps in order on the object `x`, decision 0183. C++ evaluates the object of a call first,
  // so the steps go before the statement. The arguments of a step are in its own call, so they run after the step before it. A temporary at the start gets a
  // fresh local. `Last` is whether the last step stays out of the steps and is the result, as the statement. Otherwise the result is the object.
  // A chain on anything but a local, a parameter or a temporary of a struct with no destructor of the model stays nested.
  llvm::json::Value chain(const CXXMemberCallExpr *Top, unsigned Near, bool Last) const {
    std::vector<const CXXMemberCallExpr *> Steps;
    const Expr *Base = nullptr;
    for (const CXXMemberCallExpr *Call = Top; Call;) {
      Steps.insert(Steps.begin(), Call);
      Base = Call->getImplicitObjectArgument()->IgnoreParenImpCasts();
      Call = fluentCall(Base);
    }
    const auto *Callee = dyn_cast<MemberExpr>(Steps.front()->getCallee()->IgnoreParens());
    const auto *Ref = dyn_cast<DeclRefExpr>(Base);
    const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
    llvm::json::Value Object = nullptr;
    if (!Callee || Callee->isArrow()) {
      return nested(Top, Near);
    } else if (Var && !Var->hasGlobalStorage()) {
      Object = expr(Base, Near);
    } else if (Base->isPRValue() && Base->getType()->isRecordType()) {
      const CXXRecordDecl *RD = plainStruct(Base->getType());
      const CXXDestructorDecl *D = RD ? RD->getDestructor() : nullptr;
      // A temporary of a struct with a destructor keeps its refusal, decision 0178.
      if (!RD || (D && member(D)))
        return nested(Top, Near);
      const std::string Fresh = "'chain'" + std::to_string(++Chains);
      llvm::json::Value Kind = type(Base->getType().getUnqualifiedType());
      Prelude.push_back(tag("Local", llvm::json::Array{Fresh, Kind, expr(Base, Near), number(Near)}));
      Object = tag("Var", llvm::json::Array{Fresh, Kind});
    } else {
      return nested(Top, Near);
    }
    for (size_t I = 0; I < Steps.size(); ++I) {
      const CXXMemberCallExpr *Step = Steps[I];
      llvm::json::Array Args{Object};
      for (unsigned A = 0; A < Step->getNumArgs(); ++A)
        Args.push_back(callArg(Step->getDirectCallee(), A, Step->getArg(A), Near));
      llvm::json::Value Call = tag("Call", llvm::json::Array{key(Step->getDirectCallee()), name(Step->getDirectCallee()), std::move(Args), number(Near)});
      if (Last && I + 1 == Steps.size())
        return Call;
      Prelude.push_back(std::move(Call));
    }
    return Object;
  }
  // The call that gives a value, `x.f(a).total()`, when it is the full value of a statement and its object is a chain: the one place where the steps may go
  // before the statement, decision 0183.
  const Expr *chainValue(const Stmt *S, const Expr *Value) const {
    const Expr *Call = Value ? Value->IgnoreParenImpCasts() : nullptr;
    const auto *Member = Call ? dyn_cast<CXXMemberCallExpr>(Call) : nullptr;
    return S == HoistFor && Member && !fluentCall(Call) && fluentCall(Member->getImplicitObjectArgument()) ? Call : nullptr;
  }

  llvm::json::Value stmt(const Stmt *S) const {
    // The body of a constructor cannot read or write a field, or use `this`, and it cannot return early, decision 0179. A control statement holds its
    // expressions and its statements, which come here or to `expr` themselves.
    if (InConstructorBody && !isa<IfStmt, WhileStmt, ForStmt, CXXForRangeStmt, SwitchStmt, CompoundStmt, DoStmt>(S)) {
      if (readsObject(S))
        return unknown(S, "a field in the body of a constructor", line(S->getBeginLoc()));
      if (isa<ReturnStmt>(S))
        return unknown(S, describe(S), line(S->getBeginLoc()));
    }
    if (const auto *If = dyn_cast<IfStmt>(S); If && !If->getInit() && !If->getConditionVariable() && !If->isConsteval())
      return tag("If", llvm::json::Array{expr(If->getCond(), line(S->getBeginLoc())), stmts(If->getThen()), If->getElse() ? stmts(If->getElse()) : llvm::json::Array{},
                                         number(line(S->getBeginLoc()))});
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && !Return->getRetValue())
      return tag("Exit", number(line(S->getBeginLoc())));
    // `return *this;` of a function that gives back its object is a return with no value, decision 0183.
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && isReturnThis(Return) && fluent(Enclosing))
      return tag("Exit", number(line(S->getBeginLoc())));
    // `return f();` of a void call has no rule: the return gives no value.
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue() && Return->getRetValue()->getType()->isVoidType())
      return unknown(S, describe(S), line(S->getBeginLoc()));
    // A temporary in the return of a function that returns a reference dies at the end of the return, decision 0181.
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue() && returnsReference(Return) && holdsTemporary(Return->getRetValue()))
      return unknown(S, "a temporary in the return of a function that returns a reference", line(S->getBeginLoc()));
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue())
      HoistOk = chainValue(S, Return->getRetValue());
    if (const auto *Return = dyn_cast<ReturnStmt>(S); Return && Return->getRetValue())
      return tag("Return", llvm::json::Array{expr(Return->getRetValue(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    if (const auto *Switch = dyn_cast<SwitchStmt>(S); Switch && !Switch->getInit() && !Switch->getConditionVariable() && plainEnum(Switch->getCond()->IgnoreParenImpCasts()->getType()))
      return switchOf(Switch);
    if (const auto *Decl = dyn_cast<DeclStmt>(S); Decl && Decl->isSingleDecl())
      if (const auto *Var = dyn_cast<VarDecl>(Decl->getSingleDecl()); Var && Var->hasLocalStorage() && Var->getInit()) {
        HoistOk = chainValue(S, Var->getInit());
        llvm::json::Value Start = vecMove(Var->getInit(), Var->getType());
        if (Start.getAsNull())
          Start = vecFill(Var->getInit(), line(S->getBeginLoc()));
        if (Start.getAsNull())
          Start = expr(Var->getInit(), line(S->getBeginLoc()));
        return tag("Local", llvm::json::Array{Var->getNameAsString(), varType(Var), std::move(Start), number(line(S->getBeginLoc()))});
      }
    if (const auto *Assign = dyn_cast<BinaryOperator>(S); Assign && Assign->getOpcode() == BO_Assign) {
      if (const auto *Target = dyn_cast<DeclRefExpr>(Assign->getLHS()); Target && isTarget(Target->getDecl()))
        return tag("Assign", llvm::json::Array{nameOf(Target->getDecl()), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // `v[i] = e` where `v` is a vector by reference, decision 0145. Any other write to a vector has no rule.
      if (const auto *Subscript = dyn_cast<CXXOperatorCallExpr>(Assign->getLHS()->IgnoreParens());
          Subscript && Subscript->getOperator() == OO_Subscript && Subscript->getNumArgs() == 2 && isMutSeq(Subscript->getArg(0)))
        return tag("SetIndex", llvm::json::Array{cast<DeclRefExpr>(Subscript->getArg(0)->IgnoreParenImpCasts())->getDecl()->getNameAsString(),
                                                 expr(Subscript->getArg(1), line(S->getBeginLoc())), expr(Assign->getRHS(), line(S->getBeginLoc())),
                                                 number(line(S->getBeginLoc()))});
      // A write of a field through a local `std::unique_ptr`, decision 0186. The core refuses a parameter that the body does not move.
      if (const auto [Own, Field] = ownField(Assign->getLHS()); Own)
        return tag("SetOwnField", llvm::json::Array{nameOf(Own), Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // A write of a field of a reference parameter, decision 0108.
      if (const auto [Param, Field] = refField(Assign->getLHS()); Param)
        return tag("SetRefField", llvm::json::Array{Param->getNameAsString(), Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // `f[i] = e` where `f` is a vector field of the object, decisions 0187 and 0196.
      if (const auto *Subscript = dyn_cast<CXXOperatorCallExpr>(Assign->getLHS()->IgnoreParens()); Subscript && Subscript->getOperator() == OO_Subscript && Subscript->getNumArgs() == 2)
        if (const FieldDecl *Field = objectField(Subscript->getArg(0)->IgnoreParenImpCasts()); Field && !fieldSeq(Field->getType()).isNull())
          return tag("SetFieldAt", llvm::json::Array{Field->getNameAsString(), expr(Subscript->getArg(1), line(S->getBeginLoc())), expr(Assign->getRHS(), line(S->getBeginLoc())),
                                                     number(line(S->getBeginLoc()))});
      // `f->g = e` of a `std::unique_ptr` field `f` of the object, decision 0197.
      if (const auto [Held, Field] = throughField(Assign->getLHS()); Held)
        return tag("SetThroughField", llvm::json::Array{Held->getNameAsString(), Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      // A write of a field of the object, decision 0096.
      if (const FieldDecl *Field = objectField(Assign->getLHS()))
        return tag("SetField", llvm::json::Array{Field->getNameAsString(), expr(Assign->getRHS(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    }
    // `v[i] = e` on a vector of unique_ptr has no rule yet, decision 0170.
    {
      const Stmt *Plain = S;
      if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(Plain))
        Plain = Cleanups->getSubExpr();
      // `n->f = e` of a unique_ptr field, where `e` is `std::move(x)` of a local or a `std::make_unique` call, decision 0186.
      if (const auto *Assign = dyn_cast<CXXOperatorCallExpr>(Plain); Assign && Assign->getOperator() == OO_Equal && Assign->getNumArgs() == 2)
        if (const auto [Own, Field] = ownField(Assign->getArg(0)); Own && isUniquePtr(Field->getType())) {
          llvm::json::Value Value = moveOfLocal(Assign->getArg(1), Field->getType());
          if (Value.getAsNull())
            Value = expr(Assign->getArg(1), line(S->getBeginLoc()));
          return tag("SetOwnField", llvm::json::Array{nameOf(Own), Field->getNameAsString(), std::move(Value), number(line(S->getBeginLoc()))});
        }
      if (const auto *Assign = dyn_cast<CXXOperatorCallExpr>(Plain); Assign && Assign->getOperator() == OO_Equal && Assign->getNumArgs() == 2 && isUniquePtr(Assign->getArg(0)->getType()))
        if (const auto *Element = dyn_cast<CXXOperatorCallExpr>(Assign->getArg(0)->IgnoreParenImpCasts()); Element && Element->getOperator() == OO_Subscript)
          return unknown(S, "an assignment to a unique_ptr element", line(S->getBeginLoc()));
    }
    // `x = y` for a struct, with the copy assignment that the compiler makes, is the write of the variable, decision 0108.
    if (const auto *Copy = dyn_cast<CXXOperatorCallExpr>(S); Copy && Copy->getOperator() == OO_Equal && Copy->getNumArgs() == 2 && plainStruct(Copy->getArg(0)->getType()) &&
                                                             Copy->getDirectCallee() && Copy->getDirectCallee()->isTrivial())
      if (const auto *Target = dyn_cast<DeclRefExpr>(Copy->getArg(0)->IgnoreParens()); Target && isTarget(Target->getDecl()))
        return tag("Assign", llvm::json::Array{nameOf(Target->getDecl()), expr(Copy->getArg(1), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
    // `x op= e` for `+ - * / %` on an integer local or a field of the object is `x = x op e`, with the conversions that the compiler made,
    // decision 0096.
    if (const auto *Compound = dyn_cast<CompoundAssignOperator>(S)) {
      if (llvm::json::Value Lowered = compound(Compound); !Lowered.getAsNull())
        return Lowered;
    }
    // A temporary for a computed or literal argument wraps a call in a cleanup. The statement is the call inside it.
    const Stmt *Inner = S;
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(Inner))
      Inner = Cleanups->getSubExpr();
    // A call that gives a struct with a destructor is bound as a temporary. The bind is not the call, decision 0178.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
      if (const CXXRecordDecl *RD = plainStruct(Bound->getType()); RD && RD->hasUserDeclaredDestructor())
        Inner = Bound->getSubExpr();
    // A call that gives back its object, as a statement, with the calls of a chain before it, decision 0183.
    // Only the start and the step of a `for` come here with `S` not the hoist statement. A chain there has no rule.
    if (const auto *Top = fluentCall(dyn_cast<Expr>(Inner))) {
      if (S == HoistFor)
        return chain(Top, line(S->getBeginLoc()), true);
      if (fluentCall(Top->getImplicitObjectArgument()))
        return unknown(S, "a chain of calls in the head of a for", line(S->getBeginLoc()));
      return nested(Top, line(S->getBeginLoc()));
    }
    // `v.push_back(e)` where `v` is a vector by reference, decision 0148. The other member calls of a vector have no rule.
    if (const auto *Push = dyn_cast<CXXMemberCallExpr>(Inner); Push && Push->getNumArgs() == 1 && Push->getMethodDecl() && Push->getMethodDecl()->getDeclName().isIdentifier() &&
                                                           Push->getMethodDecl()->getName() == "push_back" && Push->getImplicitObjectArgument() &&
                                                           isMutSeq(Push->getImplicitObjectArgument())) {
      // The argument is bound to a reference, so a computed value sits in a temporary that is not the value.
      const Expr *Arg = Push->getArg(0);
      if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      llvm::json::Value Pushed = expr(Arg, line(S->getBeginLoc()));
      // The conversion of `std::make_unique<D>(a)` to the unique_ptr of the interface stands as the `Wrap` alone, decision 0170.
      if (llvm::json::Object *Outer = Pushed.getAsObject())
        if (llvm::json::Array *Casted = Outer->getArray("Cast"); Casted && Casted->size() == 2 && (*Casted)[0].getAsString() == StringRef("Construct"))
          if (const llvm::json::Object *Inner = (*Casted)[1].getAsObject(); Inner && Inner->get("Wrap")) {
            llvm::json::Value Bare = std::move((*Casted)[1]);
            Pushed = std::move(Bare);
          }
      return tag("PushBack", llvm::json::Array{cast<DeclRefExpr>(Push->getImplicitObjectArgument()->IgnoreParenImpCasts())->getDecl()->getNameAsString(),
                                               std::move(Pushed), number(line(S->getBeginLoc()))});
    }
    // `f.push_back(e);` and `f.pop_back();` where `f` is a vector field of the object, decision 0191.
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(Inner); Call && Call->getMethodDecl() && Call->getMethodDecl()->getDeclName().isIdentifier() &&
                                                              Call->getImplicitObjectArgument() && isFieldVec(Call->getImplicitObjectArgument())) {
      const FieldDecl *Field = objectField(Call->getImplicitObjectArgument()->IgnoreParenImpCasts());
      if (Call->getNumArgs() == 1 && Call->getMethodDecl()->getName() == "push_back") {
        const Expr *Arg = Call->getArg(0);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        return tag("PushField", llvm::json::Array{Field->getNameAsString(), expr(Arg, line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
      }
      if (Call->getNumArgs() == 0 && Call->getMethodDecl()->getName() == "pop_back")
        return tag("PopField", llvm::json::Array{Field->getNameAsString(), number(line(S->getBeginLoc()))});
    }
    // A call that is the whole statement, `f(a);` or `o.f(a);`. Its object is the first argument, decision 0096.
    // `std::sort(v.begin(), v.end())` of a vector that the function writes is a sort of the whole of `v`, decision 0161. A comparator lambda of the element type
    // with one return is `SortBy`, decision 0162. Any other call of `std::sort`, a part of a range, another comparator, a policy or two vectors, is named by
    // what it is.
    if (const auto *Sort = dyn_cast<CallExpr>(Inner); Sort && Sort->getStmtClass() == Stmt::CallExprClass && Sort->getDirectCallee() &&
                                                       Sort->getDirectCallee()->isInStdNamespace() && Sort->getDirectCallee()->getDeclName().isIdentifier() &&
                                                       Sort->getDirectCallee()->getName() == "sort" && SM.isInSystemHeader(Sort->getDirectCallee()->getLocation())) {
      const VarDecl *Whole = nullptr;
      bool Same = Sort->getNumArgs() == 2 || Sort->getNumArgs() == 3;
      for (unsigned I = 0; Same && I < 2; ++I) {
        const auto *Member = dyn_cast<CXXMemberCallExpr>(Sort->getArg(I)->IgnoreParenImpCasts());
        const Expr *Object = Member ? Member->getImplicitObjectArgument() : nullptr;
        const auto *Ref = Object ? dyn_cast<DeclRefExpr>(Object->IgnoreParenImpCasts()) : nullptr;
        const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
        Same = Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getDeclName().isIdentifier() &&
               Member->getMethodDecl()->getName() == (I == 0 ? "begin" : "end") && Var && (isa<ParmVarDecl>(Var) || Var->hasLocalStorage()) && (!Whole || Whole == Var);
        Whole = Var;
      }
      if (Same && Sort->getNumArgs() == 2)
        return tag("Sort", llvm::json::Array{Whole->getNameAsString(), number(line(S->getBeginLoc()))});
      // A comparator lambda with two parameters of one type, decision 0162. The core compares that type with the element.
      if (Same && Sort->getNumArgs() == 3)
        if (const LambdaExpr *Lambda = lambdaArgument(Sort->getArg(2)); Lambda && Lambda->getCallOperator()->getNumParams() == 2)
          if (const ReturnStmt *Return = lambdaReturn(Lambda)) {
            const CXXMethodDecl *Operator = Lambda->getCallOperator();
            const QualType First = comparatorParameter(Operator->getParamDecl(0)), Second = comparatorParameter(Operator->getParamDecl(1));
            if (!First.isNull() && First == Second)
              return tag("SortBy", llvm::json::Array{Whole->getNameAsString(), Operator->getParamDecl(0)->getNameAsString(), Operator->getParamDecl(1)->getNameAsString(), type(First),
                                                     expr(Return->getRetValue(), line(S->getBeginLoc())), number(line(S->getBeginLoc()))});
          }
      return unknown(S, "std::sort of another form", line(S->getBeginLoc()));
    }
    // A call of a destructor in code destroys the object a second time at the end of its block, decision 0178.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(Inner); Member && Member->getMethodDecl() && isa<CXXDestructorDecl>(Member->getMethodDecl()))
      return unknown(S, "a call of a destructor", line(S->getBeginLoc()));
    if (const auto *Call = dyn_cast<CallExpr>(Inner)) {
      if (llvm::json::Value Written = expr(Call, line(S->getBeginLoc())); Written.getAsObject() && Written.getAsObject()->get("Call"))
        return Written;
      // The call with a class at a reference of its interface says why, decision 0169.
      else if (const llvm::json::Array *Why = Written.getAsObject() ? Written.getAsObject()->getArray("Unknown") : nullptr;
               Why && !Why->empty() && (*Why)[0].getAsString() == StringRef("a class as a reference to its interface"))
        return Written;
    }
    // A bare block `{ ... }` is a block of the model, decision 0178.
    if (const auto *Bare = dyn_cast<CompoundStmt>(S))
      return tag("Block", llvm::json::Array{stmts(Bare), number(line(S->getBeginLoc()))});
    if (const auto *Step = dyn_cast<UnaryOperator>(S); Step && Step->isIncrementDecrementOp())
      if (const auto *Target = dyn_cast<DeclRefExpr>(Step->getSubExpr()); Target && isTarget(Target->getDecl()))
        return tag("Step", llvm::json::Array{nameOf(Target->getDecl()), varType(Target->getDecl()), Step->isIncrementOp(),
                                             number(line(S->getBeginLoc()))});
    if (const auto *While = dyn_cast<WhileStmt>(S); While && !While->getConditionVariable())
      return tag("While", llvm::json::Array{expr(While->getCond(), line(S->getBeginLoc())), loopConds(S), stmts(While->getBody()), number(line(S->getBeginLoc()))});
    // A range-for over a read-only sequence parameter, decision 0143. The loop variable is `T x`, `const T& x`, `auto x` or `const auto& x`, with
    // `T` the element type. The core builds the loop over the indexes. A write reference, a range that is no parameter, and an element of
    // another type stay unknown.
    // A range over a vector of unique_ptr has no rule yet, decision 0170.
    if (const auto *Range = dyn_cast<CXXForRangeStmt>(S)) {
      const auto *Named = dyn_cast<DeclRefExpr>(Range->getRangeInit()->IgnoreParenImpCasts());
      const QualType Held = Named ? Named->getDecl()->getType() : Range->getRangeInit()->getType();
      if (!ownVecElement(seqElement(Held)).isNull() || !ownVecElement(mutSeq(Held)).isNull() || !ownVecElement(localVec(Held.getNonReferenceType())).isNull())
        return unknown(S, "a range-for over a vector of unique_ptr", line(S->getBeginLoc()));
    }
    if (const auto *Range = dyn_cast<CXXForRangeStmt>(S); Range && !Range->getInit() && Range->getLoopVariable() && Range->getLoopVariable()->getIdentifier())
      if (const auto *Ref = dyn_cast<DeclRefExpr>(Range->getRangeInit()->IgnoreParenImpCasts()); Ref && isa<ParmVarDecl>(Ref->getDecl()) && isSeq(Ref->getType())) {

        QualType Declared = Range->getLoopVariable()->getType();
        bool Written = false;
        if (Declared->isReferenceType()) {
          Written = !Declared->isLValueReferenceType() || !Declared->getPointeeType().isConstQualified();
          Declared = Declared->getPointeeType();
        }
        const QualType Element = seqElement(Ref->getType());
        if (!Written && Declared.getCanonicalType().getUnqualifiedType() == Element.getCanonicalType().getUnqualifiedType())
          return tag("RangeFor", llvm::json::Array{Range->getLoopVariable()->getNameAsString(), type(Element), expr(Ref, line(S->getBeginLoc())), loopConds(S),
                                                   stmts(Range->getBody()), number(line(S->getBeginLoc()))});
      }
    // A local of a struct with a destructor in the head of a `for` has no rule, decision 0178.
    if (const auto *For = dyn_cast<ForStmt>(S))
      if (const auto *Init = dyn_cast_or_null<DeclStmt>(For->getInit()))
        for (const Decl *D : Init->decls())
          if (const auto *Var = dyn_cast<VarDecl>(D))
            if (const CXXRecordDecl *RD = plainStruct(Var->getType()); RD && RD->hasUserDeclaredDestructor())
              return unknown(S, describe(S), line(S->getBeginLoc()));
    if (const auto *For = dyn_cast<ForStmt>(S); For && For->getCond() && For->getInc() && !For->getConditionVariable())
      if (const auto *Init = dyn_cast_or_null<DeclStmt>(For->getInit()); Init && Init->isSingleDecl())
        if (const auto *Var = dyn_cast<VarDecl>(Init->getSingleDecl()); Var && Var->hasLocalStorage() && Var->getInit())
          return tag("For", llvm::json::Array{stmt(Init), expr(For->getCond(), line(S->getBeginLoc())), stmt(For->getInc()), loopConds(S),
                                              stmts(For->getBody()), number(line(S->getBeginLoc()))});
    return unknown(S, describe(S), line(S->getBeginLoc()));
  }

  // A switch over a value of an enum, decision 0109: the cases in source order, each with the place of its enumerator and its statements up to the
  // next label. A `break` that ends a case is dropped. A default, a label with another label for its body, and anything before the first label stay
  // unknown, by their nodes.
  llvm::json::Value switchOf(const SwitchStmt *Switch) const {
    const unsigned At = line(Switch->getBeginLoc());
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Switch->getBody());
    if (!Body)
      return unknown(Switch, describe(Switch), At);
    const EnumDecl *ED = plainEnum(Switch->getCond()->IgnoreParenImpCasts()->getType());
    enumType(ED);
    llvm::json::Array Cases;
    std::vector<const Stmt *> Current;
    const auto close = [&]() {
      // A body in braces, with the break after them or inside them, is the statements of the block, decision 0114. Any other shape stays as it is.
      if (!Current.empty() && isa<CompoundStmt>(Current.front()) && (Current.size() == 1 || (Current.size() == 2 && isa<BreakStmt>(Current.back())))) {
        const auto Block = cast<CompoundStmt>(Current.front())->body();
        Current.assign(Block.begin(), Block.end());
      }
      if (!Current.empty() && isa<BreakStmt>(Current.back()))
        Current.pop_back();
      llvm::json::Array Out;
      for (const Stmt *Child : Current)
        pushStmt(Child, Out);
      Cases.back().getAsArray()->push_back(std::move(Out));
      Current.clear();
    };
    for (const Stmt *Child : Body->body()) {
      if (isa<DefaultStmt>(Child) || (isa<CaseStmt>(Child) && (isa<CaseStmt>(cast<CaseStmt>(Child)->getSubStmt()) || isa<DefaultStmt>(cast<CaseStmt>(Child)->getSubStmt()))))
        return unknown(Child, describe(isa<CaseStmt>(Child) ? cast<CaseStmt>(Child)->getSubStmt() : Child), line(Child->getBeginLoc()));
      if (const auto *Label = dyn_cast<CaseStmt>(Child)) {
        const auto *Name = dyn_cast<DeclRefExpr>(Label->getLHS()->IgnoreParenImpCasts());
        const auto *Enumerator = Name ? dyn_cast<EnumConstantDecl>(Name->getDecl()) : nullptr;
        if (!Enumerator || Enumerator->getDeclContext() != ED || Label->getRHS())
          return unknown(Child, describe(Child), line(Child->getBeginLoc()));
        if (!Cases.empty())
          close();
        Cases.push_back(llvm::json::Array{number(enumeratorPlace(ED, Enumerator))});
        Current.push_back(Label->getSubStmt());
      } else if (Cases.empty()) {
        return unknown(Child, describe(Child), line(Child->getBeginLoc()));
      } else {
        Current.push_back(Child);
      }
    }
    if (!Cases.empty())
      close();
    return tag("Switch", llvm::json::Array{expr(Switch->getCond()->IgnoreParenImpCasts(), At), enumKey(ED), std::move(Cases), number(At)});
  }

  // A field of a struct reference parameter, `p.f`, as the parameter and the field, or two nulls, decision 0108.
  std::pair<const ParmVarDecl *, const FieldDecl *> refField(const Expr *E) const {
    if (const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens()); Member && !Member->isArrow())
      if (const auto *Base = dyn_cast<DeclRefExpr>(Member->getBase()->IgnoreParenImpCasts()))
        if (const auto *Param = dyn_cast<ParmVarDecl>(Base->getDecl()); Param && !mutRef(Param->getType()).getAsNull())
          if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
            return {Param, Field};
    return {nullptr, nullptr};
  }

  // The field of a plain struct that an expression names on the object of a member function, `n_` or `this->n_`, or null.
  const FieldDecl *objectField(const Expr *E) const {
    if (const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens()); Member && isa<CXXThisExpr>(Member->getBase()->IgnoreParenImpCasts()))
      if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
        return Field;
    return nullptr;
  }

  // `x op= e` as the write `x = x op e`, or null when it has no rule. The left side is read, converted to the computation type, operated on,
  // and converted back, as the compiler does. The right side is already in the computation type.
  llvm::json::Value compound(const CompoundAssignOperator *C) const {
    const char *Op = nullptr;
    switch (C->getOpcode()) {
    case BO_AddAssign: Op = "Add"; break;
    case BO_SubAssign: Op = "Sub"; break;
    case BO_MulAssign: Op = "Mul"; break;
    case BO_DivAssign: Op = "Div"; break;
    case BO_RemAssign: Op = "Rem"; break;
    default: return nullptr;
    }
    const unsigned At = line(C->getBeginLoc());
    const Expr *Left = C->getLHS();
    const char *Scalar = scalar(Left->getType());
    // `x += e` of a double is the write of `x + e`, which the core refuses as a rounding, decision 0150.
    if (!isDouble(Left->getType()) && (!Scalar || StringRef(Scalar) == "Bool"))
      return nullptr;
    const auto *Name = dyn_cast<DeclRefExpr>(Left);
    const FieldDecl *Field = Name ? nullptr : objectField(Left);
    const auto [Param, RefField] = Name ? std::pair<const ParmVarDecl *, const FieldDecl *>{} : refField(Left);
    const auto [Held, Through] = Name ? std::pair<const FieldDecl *, const FieldDecl *>{} : throughField(Left);
    if (!(Name && isTarget(Name->getDecl())) && !Field && !Param && !Held)
      return nullptr;
    const auto convert = [&](llvm::json::Value V, QualType From, QualType To) -> llvm::json::Value {
      if (Context.hasSameType(From, To))
        return V;
      return tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{type(From), type(To)}), std::move(V)});
    };
    llvm::json::Value Read = tag("Cast", llvm::json::Array{"Read", expr(Left, At)});
    llvm::json::Value A = convert(std::move(Read), Left->getType(), C->getComputationLHSType());
    llvm::json::Value B = expr(C->getRHS(), At);
    llvm::json::Value Operated =
        StringRef(Op) == "Div" || StringRef(Op) == "Rem"
            ? tag("Divide", llvm::json::Array{Op, std::move(A), std::move(B), type(C->getComputationResultType())})
            : tag("Bin", llvm::json::Array{Op, std::move(A), std::move(B)});
    llvm::json::Value Value = convert(std::move(Operated), C->getComputationResultType(), Left->getType());
    if (Param)
      return tag("SetRefField", llvm::json::Array{Param->getNameAsString(), RefField->getNameAsString(), std::move(Value), number(At)});
    if (Field)
      return tag("SetField", llvm::json::Array{Field->getNameAsString(), std::move(Value), number(At)});
    if (Held)
      return tag("SetThroughField", llvm::json::Array{Held->getNameAsString(), Through->getNameAsString(), std::move(Value), number(At)});
    return tag("Assign", llvm::json::Array{nameOf(Name->getDecl()), std::move(Value), number(At)});
  }

  // A parameter or a local: the names the translator reads and writes.
  static bool isVariable(const ValueDecl *D) { return isa<ParmVarDecl>(D) || (isa<VarDecl>(D) && cast<VarDecl>(D)->hasLocalStorage()); }
  // A variable or a global: the names that a write can target, decision 0173.
  static bool isTarget(const ValueDecl *D) { return isVariable(D) || isGlobal(D); }

  // The optional that a read names, decision 0133. The compiler holds the optional that a call or a construction gives in a temporary, and
  // the read names the temporary. A reference local is refused, row lvalue_references, so the read is always copied into a value and no
  // reference outlives the temporary. Used at these reads only.
  static const Expr *optObject(const Expr *E) {
    const Expr *Inner = E;
    bool Held = false;
    for (;;) {
      if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Inner))
        Inner = Temporary->getSubExpr(), Held = true;
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
        Inner = Bound->getSubExpr(), Held = true;
      else if (const auto *Cast = dyn_cast<ImplicitCastExpr>(Inner); Cast && Cast->getCastKind() == CK_NoOp)
        Inner = Cast->getSubExpr();
      else
        return Held ? Inner : E;
    }
  }

  // A positive double as `m * 2^p` with `m` odd, or zero as (0, 0).
  static void splitDouble(double Value, uint64_t &Mantissa, int &Power) {
    int Exponent = 0;
    const double Fraction = std::frexp(Value, &Exponent);
    Mantissa = static_cast<uint64_t>(std::ldexp(Fraction, 53));
    Power = Exponent - 53;
    while (Mantissa && Mantissa % 2 == 0)
      Mantissa /= 2, ++Power;
  }
  // The value of a non-negative double as `m / q` with `q` a power of two and both in 64 bits, or false, decision 0158.
  static bool dyadic(double Value, uint64_t &M, uint64_t &Q) {
    uint64_t Mantissa;
    int Power;
    splitDouble(Value, Mantissa, Power);
    if (!Mantissa)
      return M = 0, Q = 1, true;
    if (Power >= 0) {
      const unsigned __int128 Whole = static_cast<unsigned __int128>(Mantissa) << (Power < 64 ? Power : 64);
      return Power < 64 && Whole <= UINT64_MAX ? (M = static_cast<uint64_t>(Whole), Q = 1, true) : false;
    }
    return -Power <= 63 ? (M = Mantissa, Q = uint64_t(1) << -Power, true) : false;
  }
  // The expression of a double value, or null when no form fits: `RealLit` for `d / 10^k` with `k` up to 19 and `d` in 64 bits, decision 0150, else
  // `Ratio` for `m / q`, decision 0158. A negative value is the negation of one.
  llvm::json::Value realForm(double Value) const {
    if (!std::isfinite(Value))
      return nullptr;
    if (std::signbit(Value) && Value != 0.0) {
      llvm::json::Value Inner = realForm(-Value);
      return Inner.getAsNull() ? Inner : tag("Neg", std::move(Inner));
    }
    uint64_t Mantissa;
    int Power;
    splitDouble(Value, Mantissa, Power);
    if (!Mantissa)
      return tag("RealLit", llvm::json::Array{number(0), number(0)});
    unsigned __int128 Digits = Mantissa;
    if (Power >= 0) {
      if (Power < 64 && (Digits << Power) <= UINT64_MAX)
        return tag("RealLit", llvm::json::Array{number(static_cast<uint64_t>(Digits << Power)), number(0)});
      return nullptr;
    }
    if (-Power <= 19) {
      for (int I = 0; I < -Power && Digits <= UINT64_MAX; ++I)
        Digits *= 5;
      if (Digits <= UINT64_MAX)
        return tag("RealLit", llvm::json::Array{number(static_cast<uint64_t>(Digits)), number(-Power)});
    }
    uint64_t M, Q;
    return dyadic(Value, M, Q) ? tag("Ratio", llvm::json::Array{number(M), number(Q)}) : llvm::json::Value(nullptr);
  }

  // The lambda written in a call, behind the copies and temporaries that the compiler adds, or null.
  static const LambdaExpr *lambdaArgument(const Expr *Arg) {
    for (;;) {
      Arg = Arg->IgnoreParenImpCasts();
      if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Arg))
        Arg = Wrapper->getSubExpr();
      else if (const auto *Construct = dyn_cast<CXXConstructExpr>(Arg); Construct && Construct->getNumArgs() == 1)
        Arg = Construct->getArg(0);
      else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Arg))
        Arg = Bound->getSubExpr();
      else
        return dyn_cast<LambdaExpr>(Arg);
    }
  }
  // The limits of a comparator lambda, decision 0162: captures by copy with no initializer, a call operator that is const, and a body of one
  // `return e;` of a boolean. The return statement, or null. ponytail: `countIf` keeps its own copy of these checks, because it names the limit
  // that each miss breaks, decision 0157. Upgrade: one helper that gives the first missed limit, and `countIf` maps it to its sentence.
  static const ReturnStmt *lambdaReturn(const LambdaExpr *Lambda) {
    const CXXMethodDecl *Operator = Lambda->getCallOperator();
    if (Lambda->getCaptureDefault() == LCD_ByRef || !Operator->isConst())
      return nullptr;
    for (const LambdaCapture &Capture : Lambda->captures())
      if (Capture.getCaptureKind() != LCK_ByCopy || !Capture.capturesVariable() || Lambda->isInitCapture(&Capture))
        return nullptr;
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Operator->getBody());
    const auto *Return = Body && Body->size() == 1 ? dyn_cast<ReturnStmt>(Body->body_front()) : nullptr;
    return Return && Return->getRetValue() && Return->getRetValue()->getType()->isBooleanType() ? Return : nullptr;
  }
  // The type of a comparator parameter, by value or by reference to const, with no qualifier, or null.
  static QualType comparatorParameter(const ParmVarDecl *Parameter) {
    QualType Declared = Parameter->getType();
    if (Declared->isReferenceType()) {
      if (!Declared->isLValueReferenceType() || !Declared->getPointeeType().isConstQualified())
        return QualType();
      Declared = Declared->getPointeeType();
    }
    return Parameter->getIdentifier() ? Declared.getCanonicalType().getUnqualifiedType() : QualType();
  }

  // The literal of an integer value of the type `T`, or null when the magnitude needs more than 64 bits. A negative value is the negation of a literal, as `-5` is,
  // decisions 0106 and 0186.
  llvm::json::Value intLiteral(const llvm::APSInt &Value, QualType T) const {
    // The magnitude of a negative value, taken one bit wider so that the minimum of a type does not overflow.
    llvm::APSInt Wide = Value.extend(Value.getBitWidth() + 1);
    if (Value.isNegative())
      Wide = -Wide;
    if (Wide.getActiveBits() > 64)
      return nullptr;
    const llvm::json::Value Own = type(T);
    if (!Value.isNegative())
      return tag("Lit", llvm::json::Array{number(Wide.getZExtValue()), Own});
    // A negative value is computed in int, or in long for int64_t, and converted to its type. The minimum of int and of long is
    // the negation of the maximum, less 1, so that no literal is too large.
    const bool Long = Value.getBitWidth() > 32;
    const char *Computed = Long ? "I64" : "I32";
    const uint64_t Maximum = Long ? INT64_MAX : INT32_MAX;
    llvm::json::Value Negative = Wide.getZExtValue() <= Maximum
                                     ? tag("Neg", tag("Lit", llvm::json::Array{number(Wide.getZExtValue()), Computed}))
                                     : tag("Bin", llvm::json::Array{"Sub", tag("Neg", tag("Lit", llvm::json::Array{number(Maximum), Computed})),
                                                                    tag("Lit", llvm::json::Array{number(1), Computed})});
    if (StringRef(Computed) == Own.getAsString().value_or(""))
      return Negative;
    return tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{Computed, Own}), std::move(Negative)});
  }
  // The kind of a cast of a final class over an interface to one of its interfaces, or null, decision 0166.
  llvm::json::Value upcastKind(const CastExpr *Cast) const {
    const CXXRecordDecl *To = Cast->getType()->getAsCXXRecordDecl();
    const CXXRecordDecl *From = Cast->getSubExpr()->getType()->getAsCXXRecordDecl();
    if (!To || !From || !finalOverInterface(From) || !isInterface(To))
      return nullptr;
    return upcastJson(From, To);
  }
  // The kind `Upcast(D, B)` of a final class over interfaces to one of its interfaces, or null, decisions 0166 and 0168.
  llvm::json::Value upcastJson(const CXXRecordDecl *From, const CXXRecordDecl *To) const {
    if (!From || !To || !finalOverInterface(From) || !isInterface(To))
      return nullptr;
    for (const CXXRecordDecl *B : interfaceBases(From))
      if (B->getCanonicalDecl() == To->getCanonicalDecl()) {
        type(Context.getRecordType(From));
        interfaceEntry(B);
        return tag("Upcast", llvm::json::Array{structKey(From->getDefinition()), structKey(B)});
      }
    return nullptr;
  }
  // The construction `new T(args)` in the body of an instantiated `std::make_unique<T>`, or null.
  static const CXXConstructExpr *constructedByNew(const Stmt *S) {
    if (!S)
      return nullptr;
    if (const auto *New = dyn_cast<CXXNewExpr>(S))
      return New->getConstructExpr();
    for (const Stmt *Child : S->children())
      if (const CXXConstructExpr *Found = constructedByNew(Child))
        return Found;
    return nullptr;
  }
  // `n->f` where `n` is a local, or a parameter by value, of type `std::unique_ptr<S>` for a plain struct `S`: the pair (`n`, `f`). A pair of nulls for any other form,
  // such as a reference parameter or the field of a field, decision 0186.
  std::pair<const VarDecl *, const FieldDecl *> ownField(const Expr *E) const {
    const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens());
    const auto *Field = Member ? dyn_cast<FieldDecl>(Member->getMemberDecl()) : nullptr;
    const auto *Arrow = Member && Member->isArrow() ? dyn_cast<CXXOperatorCallExpr>(Member->getBase()->IgnoreParenImpCasts()) : nullptr;
    if (!Field || !Arrow || Arrow->getOperator() != OO_Arrow || Arrow->getNumArgs() != 1)
      return {};
    const auto *Ref = dyn_cast<DeclRefExpr>(Arrow->getArg(0)->IgnoreParenImpCasts());
    const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
    if (!Var || !Var->hasLocalStorage() || Var->getType()->isReferenceType() || Var->getType().isConstQualified())
      return {};
    const QualType Held = ownElement(Var->getType());
    if (Held.isNull() || !plainStruct(Held))
      return {};
    return {Var, Field};
  }
  // `f->g` where `f` is a `std::unique_ptr` field of the object that owns a plain struct: the pair (`f`, `g`). A pair of nulls for any other form, such as the field of a
  // parameter, decision 0197.
  std::pair<const FieldDecl *, const FieldDecl *> throughField(const Expr *E) const {
    const auto *Member = dyn_cast<MemberExpr>(E->IgnoreParens());
    const auto *Field = Member ? dyn_cast<FieldDecl>(Member->getMemberDecl()) : nullptr;
    const auto *Arrow = Member && Member->isArrow() ? dyn_cast<CXXOperatorCallExpr>(Member->getBase()->IgnoreParenImpCasts()) : nullptr;
    if (!Field || !Arrow || Arrow->getOperator() != OO_Arrow || Arrow->getNumArgs() != 1)
      return {};
    const FieldDecl *Held = objectField(Arrow->getArg(0)->IgnoreParenImpCasts());
    if (!Held || !isUniquePtr(Held->getType()) || Held->getType().isConstQualified())
      return {};
    const QualType Owned = ownElement(Held->getType());
    if (Owned.isNull() || !plainStruct(Owned))
      return {};
    return {Held, Field};
  }
  // `std::make_unique<S>()` of a plain struct `S`: `Wrap(Construct(S, values))` with the start value of each field, decision 0186. An integer or bool field starts with its
  // default member initializer, which must be a constant expression. A `std::unique_ptr` field with no initializer, or with `nullptr`, starts null. Null for any other form.
  llvm::json::Value makeUniqueNew(const CallExpr *Make) const {
    const QualType Made = ownElement(Make->getType());
    const CXXRecordDecl *RD = Made.isNull() ? nullptr : plainStruct(Made);
    if (!RD || finalOverInterface(RD) || !SM.isInSystemHeader(Make->getDirectCallee()->getLocation()))
      return nullptr;
    // A constructor of its own may set any field, so the start values would not be those of the initializers.
    for (const CXXConstructorDecl *C : RD->ctors())
      if (C->isDefaultConstructor() && C->isUserProvided())
        return nullptr;
    llvm::json::Array Values;
    for (const FieldDecl *F : RD->fields()) {
      const QualType FT = F->getType();
      const Expr *Init = F->hasInClassInitializer() ? F->getInClassInitializer() : nullptr;
      if (!ownVecElement(FT).isNull()) {
        // The initializer `nullptr` is a conversion of the null literal to the unique_ptr.
        if (Init) {
          Init = Init->IgnoreParenImpCasts();
          if (const auto *Construct = dyn_cast<CXXConstructExpr>(Init); Construct && Construct->getNumArgs() == 1)
            Init = Construct->getArg(0)->IgnoreParenImpCasts();
          if (!isa<CXXNullPtrLiteralExpr>(Init))
            return nullptr;
        }
        Values.push_back("Nullopt");
        continue;
      }
      const char *Scalar = scalar(FT) ? scalar(FT) : smallScalar(FT);
      // A constant expression of C++11 has no overflow and no side effect, so `2147483647 + 1` and `(g = 9, 4)` keep the sentence of today.
      APValue Value;
      if (!Scalar || !Init || Init->isValueDependent() || !Init->isCXX11ConstantExpr(Context, &Value) || !Value.isInt())
        return nullptr;
      if (StringRef(Scalar) == "Bool") {
        Values.push_back(tag("Bool", Value.getInt().getBoolValue()));
        continue;
      }
      llvm::json::Value Literal = intLiteral(Value.getInt(), FT.getCanonicalType().getUnqualifiedType());
      if (Literal.getAsNull())
        return nullptr;
      Values.push_back(std::move(Literal));
    }
    (void)type(Made);  // writes the struct
    return tag("Wrap", tag("Construct", llvm::json::Array{structKey(RD), std::move(Values)}));
  }
  // `std::move(x)` of a local or a parameter `x` whose type is exactly the `std::unique_ptr<B>` type `Target`: `Move(x, Own(B))`, decision 0171. Null for any other form.
  // The name of a local or a parameter by value as an xvalue, with no `std::move` call, is the implicit move of `return x;`, which gives the same `Move`, decision 0186.
  llvm::json::Value moveOfLocal(const Expr *Moved, QualType Target) const {
    const auto *Call = dyn_cast<CallExpr>(Moved->IgnoreParenImpCasts());
    const FunctionDecl *Callee = Call && Call->getNumArgs() == 1 ? Call->getDirectCallee() : nullptr;
    const auto *Implicit = dyn_cast<ImplicitCastExpr>(Moved->IgnoreParens());
    const bool Moves = Callee && Callee->isInStdNamespace() && Callee->getDeclName().isIdentifier() && Callee->getName() == "move";
    const bool Returns = !Call && Implicit && Implicit->isXValue() && Implicit->getCastKind() == CK_NoOp;
    if (!Moves && !Returns)
      return nullptr;
    const auto *Ref = dyn_cast<DeclRefExpr>((Moves ? Call->getArg(0) : Moved)->IgnoreParenImpCasts());
    const auto *Var = Ref ? dyn_cast<VarDecl>(Ref->getDecl()) : nullptr;
    if (!Var || !Var->hasLocalStorage() || Var->getType()->isReferenceType() || Var->getType().hasQualifiers() ||
        Var->getType().getCanonicalType() != Target.getUnqualifiedType().getCanonicalType())
      return nullptr;
    const QualType Held = ownVecElement(Var->getType());
    if (Held.isNull())
      return nullptr;
    // The implicit move of a pointer to an interface keeps the refusal of decision 0168. Decision 0186 names the struct.
    if (!Moves && isInterface(ownElement(Held)->getAsCXXRecordDecl()))
      return nullptr;
    return tag("Move", llvm::json::Array{Var->getNameAsString(), tag("Own", ownScalar(ownElement(Held)))});
  }
  // The call of the value constructor that `std::make_unique` makes, `Call(key, name, args, line)`, for `Constructed`, the construction in the body of the
  // instance of `make_unique`. Each argument has exactly the type of its parameter, so the construction converts nothing. Null for any other form.
  llvm::json::Value constructedCall(const CallExpr *Make, const CXXConstructExpr *Constructed, unsigned Near, unsigned At) const {
    if (!Constructed || !valueConstructor(Constructed->getConstructor()) || Constructed->getConstructor()->getNumParams() != Make->getNumArgs())
      return nullptr;
    llvm::json::Array Args;
    for (unsigned I = 0; I < Make->getNumArgs(); ++I) {
      const Expr *A = Make->getArg(I);
      if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(A))
        A = Temporary->getSubExpr();
      if (A->getType().getUnqualifiedType().getCanonicalType() != Constructed->getConstructor()->getParamDecl(I)->getType().getNonReferenceType().getUnqualifiedType().getCanonicalType())
        return nullptr;
      // An argument `std::move(x)` of a local at a parameter by value of its own unique_ptr type is a move, decision 0171.
      // A parameter by reference binds the xvalue and moves nothing, so that `std::move` keeps its refusal.
      const QualType ParamType = Constructed->getConstructor()->getParamDecl(I)->getType();
      if (llvm::json::Value Moved = ParamType->isReferenceType() ? llvm::json::Value(nullptr) : moveOfLocal(A, ParamType); !Moved.getAsNull())
        Args.push_back(std::move(Moved));
      else
        Args.push_back(expr(A, Near));
    }
    const CXXConstructorDecl *C = Constructed->getConstructor();
    return tag("Call", llvm::json::Array{key(C), name(C), std::move(Args), number(At)});
  }
  // `std::make_unique<S>(args)` of a plain struct `S` with a value constructor, with arguments that have exactly the types of its parameters: `Wrap(Call(...))`,
  // decision 0197. Null for any other form.
  llvm::json::Value makeUniqueCall(const CallExpr *Make, unsigned Near) const {
    const QualType Made = ownElement(Make->getType());
    const CXXRecordDecl *RD = Made.isNull() ? nullptr : plainStruct(Made);
    if (!RD || finalOverInterface(RD) || !SM.isInSystemHeader(Make->getDirectCallee()->getLocation()))
      return nullptr;
    llvm::json::Value Built = constructedCall(Make, constructedByNew(Make->getDirectCallee()->getBody()), Near, line(Make->getBeginLoc()));
    if (Built.getAsNull())
      return nullptr;
    (void)type(Made);  // writes the struct
    return tag("Wrap", std::move(Built));
  }
  // `std::make_unique<D>(args)` of a final class over an interface, as a `std::unique_ptr<B>` of that interface: `Some(f_D'B(d))` where `d` is the value that the
  // constructor of D gives, or `S_D()` for a class with no field and no constructor, decision 0168. Null for any other form.
  llvm::json::Value makeUniqueUpcast(const CXXConstructExpr *Convert, unsigned Near) const {
    const QualType Into = ownElement(Convert->getType());
    const CXXRecordDecl *Base = Into.isNull() ? nullptr : Into->getAsCXXRecordDecl();
    if (!Base || !isInterface(Base) || Convert->getNumArgs() != 1)
      return nullptr;
    // The argument is the unique_ptr<D> that a call of make_unique gives, behind the temporaries.
    const Expr *Arg = Convert->getArg(0);
    for (;;) {
      Arg = Arg->IgnoreParenImpCasts();
      if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Arg))
        Arg = Wrapper->getSubExpr();
      else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
        Arg = Temporary->getSubExpr();
      else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Arg))
        Arg = Bound->getSubExpr();
      else
        break;
    }
    const auto *Make = dyn_cast<CallExpr>(Arg);
    const FunctionDecl *Callee = Make ? Make->getDirectCallee() : nullptr;
    if (!Callee || !Callee->isInStdNamespace() || !Callee->getDeclName().isIdentifier() || Callee->getName() != "make_unique" || !SM.isInSystemHeader(Callee->getLocation()))
      return nullptr;
    const QualType Made = ownElement(Make->getType());
    const CXXRecordDecl *Derived = Made.isNull() ? nullptr : Made->getAsCXXRecordDecl();
    if (!Derived || !plainStruct(Made))
      return nullptr;
    llvm::json::Value Kind = upcastJson(Derived, Base);
    if (Kind.getAsNull())
      return nullptr;
    // The value of D: a class with no field and no constructor of its own is `S_D()`, else the value constructor that make_unique calls.
    llvm::json::Value Built = nullptr;
    const CXXConstructExpr *Constructed = constructedByNew(Callee->getBody());
    if (Derived->field_empty() && !Derived->hasUserDeclaredConstructor() && Make->getNumArgs() == 0) {
      Built = tag("Construct", llvm::json::Array{structKey(Derived->getDefinition()), llvm::json::Array{}});
    } else {
      Built = constructedCall(Make, Constructed, Near, line(Convert->getBeginLoc()));
    }
    if (Built.getAsNull())
      return nullptr;
    return tag("Wrap", tag("Cast", llvm::json::Array{std::move(Kind), std::move(Built)}));
  }

  // The `CountIf` node of a call of `std::count_if` from the library, decision 0149, or null. When the call misses a limit of 0149, `Limit` names the first
  // limit that it misses, in the order of decision 0157. A miss that fits none of them leaves `Limit` empty, and the call stays a call with no model.
  llvm::json::Value countIf(const Expr *E, unsigned Near, std::string &Limit) const {
    const auto *Call = dyn_cast<CallExpr>(E);
    const FunctionDecl *Callee = Call && Call->getStmtClass() == Stmt::CallExprClass ? Call->getDirectCallee() : nullptr;
    if (!Callee || !Callee->isInStdNamespace() || !Callee->getDeclName().isIdentifier() || Callee->getName() != "count_if" || Call->getNumArgs() != 3 ||
        !SM.isInSystemHeader(Callee->getLocation()))
      return nullptr;
    // Both ends come from one sequence parameter.
    const ParmVarDecl *Sequence = nullptr;
    for (const char *Method : {"begin", "end"}) {
      const auto *Member = dyn_cast<CXXMemberCallExpr>(Call->getArg(Method[0] == 'b' ? 0 : 1)->IgnoreParenImpCasts());
      const Expr *Object = Member ? Member->getImplicitObjectArgument() : nullptr;
      const auto *Ref = Object ? dyn_cast<DeclRefExpr>(Object->IgnoreParenImpCasts()) : nullptr;
      const auto *Param = Ref ? dyn_cast<ParmVarDecl>(Ref->getDecl()) : nullptr;
      if (!Member || Member->getNumArgs() != 0 || !Member->getMethodDecl() || !Member->getMethodDecl()->getDeclName().isIdentifier() ||
          Member->getMethodDecl()->getName() != Method || !Param || !(isSeq(Object->getType()) || isMutSeq(Object)) || (Sequence && Sequence != Param)) {
        Limit = "count_if over a range other than v.begin(), v.end() of one sequence parameter";
        return nullptr;
      }
      Sequence = Param;
    }
    // The lambda is written in the call, behind the copies and temporaries that the compiler adds.
    const LambdaExpr *Lambda = lambdaArgument(Call->getArg(2));
    if (!Lambda) {
      Limit = "count_if with a function or a functor in place of a lambda written in the call";
      return nullptr;
    }
    const CXXMethodDecl *Operator = Lambda->getCallOperator();
    // The parameter has the element type, by value or by reference to const. A lambda with another count of parameters misses this limit too.
    QualType Element = seqElement(Sequence->getType());
    // A vector by reference that the function writes is no const sequence, so its element comes from the vector itself, decision 0145.
    if (Element.isNull() && !mutSeq(Sequence->getType()).isNull())
      Element = cast<ClassTemplateSpecializationDecl>(Sequence->getType()->getPointeeType()->getAsCXXRecordDecl())->getTemplateArgs()[0].getAsType();
    const ParmVarDecl *Parameter = Operator->getNumParams() == 1 ? Operator->getParamDecl(0) : nullptr;
    QualType Declared = Parameter ? Parameter->getType() : QualType();
    if (!Declared.isNull() && Declared->isReferenceType()) {
      const bool ConstRef = Declared->isLValueReferenceType() && Declared->getPointeeType().isConstQualified();
      Declared = ConstRef ? Declared->getPointeeType() : QualType();
    }
    if (!Parameter || Declared.isNull() || Element.isNull() || !Parameter->getIdentifier() ||
        Declared.getCanonicalType().getUnqualifiedType() != Element.getCanonicalType().getUnqualifiedType()) {
      Limit = "count_if with a lambda whose parameter is not the element type";
      return nullptr;
    }
    // The captures are by copy, and none has an initializer. A capture by reference, of `this`, and a mutable lambda stay a call with no model.
    if (Lambda->getCaptureDefault() == LCD_ByRef || !Operator->isConst())
      return nullptr;
    for (const LambdaCapture &Capture : Lambda->captures()) {
      if (Capture.capturesVariable() && Lambda->isInitCapture(&Capture)) {
        Limit = "count_if with an init capture in its lambda";
        return nullptr;
      }
      if (Capture.getCaptureKind() != LCK_ByCopy || !Capture.capturesVariable())
        return nullptr;
    }
    // One `return e;` of a boolean.
    const auto *Body = dyn_cast_or_null<CompoundStmt>(Operator->getBody());
    const auto *Return = Body && Body->size() == 1 ? dyn_cast<ReturnStmt>(Body->body_front()) : nullptr;
    if (!Return || !Return->getRetValue()) {
      Limit = "count_if with a lambda whose body is more than one return";
      return nullptr;
    }
    if (!Return->getRetValue()->getType()->isBooleanType())
      return nullptr;
    return tag("CountIf", llvm::json::Array{expr(cast<CXXMemberCallExpr>(Call->getArg(0)->IgnoreParenImpCasts())->getImplicitObjectArgument()->IgnoreParenImpCasts(), Near),
                                            Parameter->getNameAsString(), type(Element), expr(Return->getRetValue(), Near)});
  }

  // The argument `std::move(x)` of a local or a parameter `x` of a plain struct, at a parameter `T&&` of a plain struct, is `x`: the callee writes it back,
  // decision 0179. The same holds for a vector `x` at a parameter `std::vector<T>&&`, decision 0185. Any other argument is its expression.
  llvm::json::Value callArg(const FunctionDecl *Callee, unsigned I, const Expr *Arg, unsigned Near) const {
    // A vector at a parameter by value, decision 0194. `std::move(v)` of a local vector or a vector parameter by value is `Move(v, type)`: the core gives the argument
    // the value, then `v` any value. A plain `v` is the variable: a copy, and `v` keeps its value.
    if (Callee && I < Callee->getNumParams())
      if (const QualType Element = paramVec(Callee->getParamDecl(I)->getType()); !Element.isNull()) {
        const Expr *Source = Arg->IgnoreParenImpCasts();
        if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Source))
          Source = Bound->getSubExpr()->IgnoreParenImpCasts();
        if (const auto *Construct = dyn_cast<CXXConstructExpr>(Source); Construct && Construct->getNumArgs() == 1 && !Construct->isListInitialization() &&
                                                                         sameElement(localVec(Construct->getType()), Element)) {
          const Expr *Inner = Construct->getArg(0)->IgnoreParenImpCasts();
          if (Construct->getConstructor()->isMoveConstructor())
            if (llvm::json::Value Moved = vecMoveOf(Inner, Element); !Moved.getAsNull())
              return Moved;
          if (Construct->getConstructor()->isCopyConstructor())
            if (const auto *Ref = dyn_cast<DeclRefExpr>(Inner); Ref && sameElement(sourceVec(Ref->getDecl()), Element) && mutSeq(Ref->getDecl()->getType()).isNull())
              return expr(Ref, Near);
        }
      }
    if (Callee && I < Callee->getNumParams() && Callee->getParamDecl(I)->getType()->isRValueReferenceType() &&
        (!mutRef(Callee->getParamDecl(I)->getType()).getAsNull() || !mutSeq(Callee->getParamDecl(I)->getType()).isNull()))
      if (const auto *Move = dyn_cast<CallExpr>(Arg->IgnoreParenImpCasts()); Move && Move->getNumArgs() == 1 && Move->getDirectCallee() &&
                                                                              Move->getDirectCallee()->isInStdNamespace() && Move->getDirectCallee()->getDeclName().isIdentifier() &&
                                                                              Move->getDirectCallee()->getName() == "move")
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Move->getArg(0)->IgnoreParenImpCasts());
            Ref && (isa<ParmVarDecl>(Ref->getDecl()) || (isa<VarDecl>(Ref->getDecl()) && cast<VarDecl>(Ref->getDecl())->hasLocalStorage())) &&
            (plainStruct(Ref->getType()) || sameElement(sourceVec(Ref->getDecl()), mutSeq(Callee->getParamDecl(I)->getType()))))
          return expr(Ref, Near);
    // A temporary of a plain struct with no destructor of the model, at a parameter `const T&`, is its value, decision 0181. Any other place keeps its refusal.
    if (Callee && I < Callee->getNumParams() && Callee->getParamDecl(I)->getType()->isLValueReferenceType() &&
        Callee->getParamDecl(I)->getType()->getPointeeType().isConstQualified()) {
      if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(Arg))
        if (const CXXRecordDecl *RD = plainStruct(Held->getType())) {
          const CXXDestructorDecl *D = RD->getDestructor();
          if (!(D && member(D)))
            return expr(Held->getSubExpr(), Near);
        }
      // A scalar temporary, `s.push(1)`, is its value as well, because the parameter `const T&` of a scalar is the scalar by value, decision 0175.
      if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(Arg); Held && (scalar(Held->getType().getUnqualifiedType()) || smallScalar(Held->getType().getUnqualifiedType())))
        return expr(Held->getSubExpr(), Near);
    }
    return expr(Arg, Near);
  }

  llvm::json::Value expr(const Expr *E, unsigned Near) const {
    if (InConstructorBody && readsObject(E))
      return unknown(E, "a field in the body of a constructor", Near);
    // The result of a call that gives back its object is the object of a call, or a statement, and both are read before this. Any other use has no rule, decision 0183.
    if (fluentCall(E) == E)
      return tag("Unknown", llvm::json::Array{"the result of a call that gives back its object, used as a value", number(Near)});
    // A temporary that needs a cleanup, such as an optional made from `x + 1`, wraps the expression. The wrapper is not the construct.
    if (const auto *Cleanups = dyn_cast<ExprWithCleanups>(E))
      return expr(Cleanups->getSubExpr(), Near);
    // A temporary of a struct with a destructor is bound for its destructor. The bind is not the value, decision 0178.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E))
      if (const CXXRecordDecl *RD = plainStruct(Bound->getType()); RD && RD->hasUserDeclaredDestructor())
        return expr(Bound->getSubExpr(), Near);
    // A std::array that a call gives is held in a temporary, which is not the value, decision 0175.
    if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(E); Held && isStdArray(Held->getType()) && isSeq(Held->getType()))
      return expr(Held->getSubExpr(), Near);
    // A vector that a call gives is held in a temporary, which is not the value, decision 0163.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E); Bound && !localVec(Bound->getType()).isNull())
      return expr(Bound->getSubExpr(), Near);
    // A `unique_ptr` that a call gives is held in a temporary, which is not the value, decision 0142.
    if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(E); Bound && isOwn(Bound->getType()))
      return expr(Bound->getSubExpr(), Near);
    if (const auto *Held = dyn_cast<MaterializeTemporaryExpr>(E); Held && isOwn(Held->getType()))
      return expr(Held->getSubExpr(), Near);
    // `std::make_unique<D>(args)` of a final class over an interface, as a `std::unique_ptr<B>`, decision 0168.
    if (const auto *Convert = dyn_cast<CXXConstructExpr>(E))
      if (llvm::json::Value Made = makeUniqueUpcast(Convert, Near); !Made.getAsNull())
        return Made;
    // `std::move(x)` of a local or a parameter `x` of exactly the type `std::unique_ptr<B>`, where C++ runs the move constructor of the unique_ptr on it, decision 0171.
    // Any other `std::move` keeps its refusal. So does `std::move` at a parameter `const std::unique_ptr<B>&`, which has no move constructor at all.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && Construct->getConstructor()->isMoveConstructor() &&
                                                               !ownVecElement(Construct->getType()).isNull())
      if (llvm::json::Value Moved = moveOfLocal(Construct->getArg(0), Construct->getType()); !Moved.getAsNull())
        return Moved;
    // The move constructor of a unique_ptr over any other `std::move` keeps the refusal of that call, decision 0171.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && Construct->getConstructor()->isMoveConstructor() &&
                                                               !ownVecElement(Construct->getType()).isNull())
      if (const auto *Move = dyn_cast<CallExpr>(Construct->getArg(0)->IgnoreParenImpCasts()); Move && Move->getDirectCallee() && Move->getDirectCallee()->isInStdNamespace() &&
                                                                                          Move->getDirectCallee()->getDeclName().isIdentifier() && Move->getDirectCallee()->getName() == "move")
        return expr(Move, Near);
    // The converting constructor of a unique_ptr of an interface from a unique_ptr of another class keeps its argument: the call that gives it is refused, as it was
    // before, decision 0168.
    if (const auto *Convert = dyn_cast<CXXConstructExpr>(E); Convert && Convert->getNumArgs() == 1 && isOwn(Convert->getType()) && isUniquePtr(Convert->getArg(0)->getType()) &&
                                                             Convert->getArg(0)->getType().getUnqualifiedType().getCanonicalType() != Convert->getType().getUnqualifiedType().getCanonicalType())
    {
      const Expr *Inner = Convert->getArg(0);
      for (;;) {
        Inner = Inner->IgnoreParenImpCasts();
        if (const auto *Wrapper = dyn_cast<ExprWithCleanups>(Inner))
          Inner = Wrapper->getSubExpr();
        else if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Inner))
          Inner = Temporary->getSubExpr();
        else if (const auto *Bound = dyn_cast<CXXBindTemporaryExpr>(Inner))
          Inner = Bound->getSubExpr();
        else
          break;
      }
      // Only a call of the library keeps its own refusal. A unique_ptr of a class that a function of the file gives would be a unique_ptr of the wrong type.
      const auto *Gives = dyn_cast<CallExpr>(Inner);
      if (Gives && Gives->getDirectCallee() && Gives->getDirectCallee()->isInStdNamespace())
        return expr(Inner, Near);
      return unknown(E, "a std::unique_ptr of a class as a std::unique_ptr of its interface", Near);
    }
    // `std::make_unique<S>()` of a plain struct is a new value with the start value of each field, decision 0186.
    if (const auto *Make = dyn_cast<CallExpr>(E); Make && Make->getNumArgs() == 0 && Make->getDirectCallee() && Make->getDirectCallee()->isInStdNamespace() &&
                                                  Make->getDirectCallee()->getDeclName().isIdentifier() && Make->getDirectCallee()->getName() == "make_unique")
      if (llvm::json::Value Made = makeUniqueNew(Make); !Made.getAsNull())
        return Made;
    // `std::make_unique<S>(args)` of a plain struct with a value constructor is the call of that constructor, decision 0197.
    if (const auto *Make = dyn_cast<CallExpr>(E); Make && Make->getNumArgs() > 0 && Make->getDirectCallee() && Make->getDirectCallee()->isInStdNamespace() &&
                                                  Make->getDirectCallee()->getDeclName().isIdentifier() && Make->getDirectCallee()->getName() == "make_unique")
      if (llvm::json::Value Made = makeUniqueCall(Make, Near); !Made.getAsNull())
        return Made;
    // `std::make_unique<T>(x)` of a scalar, with an argument of exactly that type, is a value of `x`, decision 0142.
    if (const auto *Make = dyn_cast<CallExpr>(E); Make && Make->getNumArgs() == 1 && Make->getDirectCallee() && Make->getDirectCallee()->isInStdNamespace() &&
                                                  Make->getDirectCallee()->getDeclName().isIdentifier() && Make->getDirectCallee()->getName() == "make_unique")
      if (const QualType Elem = ownElement(Make->getType()); !Elem.isNull() && scalar(Elem)) {
        const Expr *Arg = Make->getArg(0);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        if (Arg->getType().getUnqualifiedType().getCanonicalType() == Elem.getCanonicalType())
          return tag("Wrap", expr(Arg, Near));
      }
    // `p == nullptr` and `p != nullptr` of a `unique_ptr` test for a value, also with the null on the left, decision 0142. Two `unique_ptr`s
    // have no rule. C++20 rewrites `p != nullptr`, `nullptr != p` and `nullptr == p` to a `CXXRewrittenBinaryOperator`, and the test reads its
    // decomposed form. `p == nullptr` is the operator call itself.
    if (const auto *Rewritten = dyn_cast<CXXRewrittenBinaryOperator>(E)) {
      const auto Form = Rewritten->getDecomposedForm();
      if (Form.Opcode == BO_EQ || Form.Opcode == BO_NE) {
        const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Form.LHS->IgnoreParenImpCasts());
        const bool NullRight = isa<CXXNullPtrLiteralExpr>(Form.RHS->IgnoreParenImpCasts());
        const Expr *Pointer = NullLeft ? Form.RHS : Form.LHS;
        if (NullLeft != NullRight && isOwn(Pointer->getType())) {
          const char *Op = Form.Opcode == BO_EQ ? "Eq" : "Ne";
          return tag("Bin", NullRight ? llvm::json::Array{Op, expr(optObject(Pointer), Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(optObject(Pointer), Near)});
        }
      }
    }
    if (const auto *Test = dyn_cast<CXXOperatorCallExpr>(E); Test && Test->getNumArgs() == 2 && (Test->getOperator() == OO_EqualEqual || Test->getOperator() == OO_ExclaimEqual)) {
      const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Test->getArg(0)->IgnoreParenImpCasts());
      const bool NullRight = isa<CXXNullPtrLiteralExpr>(Test->getArg(1)->IgnoreParenImpCasts());
      const Expr *Pointer = NullLeft ? Test->getArg(1) : Test->getArg(0);
      if (NullLeft != NullRight && isOwn(Pointer->getType())) {
        const char *Op = Test->getOperator() == OO_EqualEqual ? "Eq" : "Ne";
        return tag("Bin", NullRight ? llvm::json::Array{Op, expr(optObject(Pointer), Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(optObject(Pointer), Near)});
      }
    }
    if (const auto *Flag = dyn_cast<CXXBoolLiteralExpr>(E))
      return tag("Bool", Flag->getValue());
    // A literal of type double is `d / 10^k` of decision 0150, or `m / q` with `q` a power of two, decision 0158. Any other stays unknown.
    if (const auto *Real = dyn_cast<FloatingLiteral>(E); Real && isDouble(Real->getType())) {
      if (llvm::json::Value Form = realForm(Real->getValueAsApproximateDouble()); !Form.getAsNull())
        return Form;
      return unknown(E, "a double literal that the model cannot write exactly", Near);
    }
    if (const auto *Literal = dyn_cast<IntegerLiteral>(E); Literal && Literal->getValue().getActiveBits() <= 64)
      return tag("Lit", llvm::json::Array{number(Literal->getValue().getZExtValue()), type(Literal->getType())});
    if (const auto *Ref = dyn_cast<DeclRefExpr>(E)) {
      const ValueDecl *D = Ref->getDecl();
      if (isa<ParmVarDecl>(D) || (isa<VarDecl>(D) && cast<VarDecl>(D)->hasLocalStorage()) || isGlobal(D))
        return tag("Var", llvm::json::Array{nameOf(D), varType(D)});
      // An enumerator of such an enum is its place among the enumerators, decision 0109.
      if (const auto *Enumerator = dyn_cast<EnumConstantDecl>(D))
        if (const auto *ED = dyn_cast<EnumDecl>(Enumerator->getDeclContext()); ED && plainEnum(Context.getTypeDeclType(ED)) == ED->getDefinition()) {
          enumType(ED);
          return tag("Enumerator", llvm::json::Array{enumKey(ED), number(enumeratorPlace(ED, Enumerator))});
        }
      // An enumerator of a valued enum is its value, a literal of the underlying integer, decision 0175.
      if (const auto *Enumerator = dyn_cast<EnumConstantDecl>(D))
        if (const auto *ED = dyn_cast<EnumDecl>(Enumerator->getDeclContext()); ED && valuedEnum(Context.getTypeDeclType(ED)) == ED->getDefinition())
          return tag("Lit", llvm::json::Array{number(Enumerator->getInitVal().getZExtValue()), valuedType(ED)});
      // A named double constant is its value as a literal is, decision 0158.
      if (const std::optional<double> Real = realConstant(D)) {
        if (llvm::json::Value Form = realForm(*Real); !Form.getAsNull())
          return Form;
        return unknown(E, "a double constant that the model cannot write exactly", Near);
      }
      // A named constant is its value, decision 0106. A negative one is the negation of a literal, as `-5` is.
      if (const std::optional<llvm::APSInt> Value = constant(D))
        if (llvm::json::Value Literal = intLiteral(*Value, D->getType().getCanonicalType().getUnqualifiedType()); !Literal.getAsNull())
          return Literal;
    }
    // A character is an integer once the compiler has converted it, decision 0106. An ASCII character only: the sign of `char` plays no part.
    if (const auto *Convert = dyn_cast<ImplicitCastExpr>(E); Convert && Convert->getCastKind() == CK_IntegralCast)
      if (const auto *Char = dyn_cast<CharacterLiteral>(Convert->getSubExpr()->IgnoreParens());
          Char && Char->getKind() == CharacterLiteralKind::Ascii && Char->getValue() < 0x80)
        return tag("Lit", llvm::json::Array{number(Char->getValue()), type(Convert->getType())});
    if (const auto *Binary = dyn_cast<BinaryOperator>(E)) {
      const char *Op = nullptr;
      switch (Binary->getOpcode()) {
      case BO_Add: Op = "Add"; break;
      case BO_Sub: Op = "Sub"; break;
      case BO_Mul: Op = "Mul"; break;
      case BO_LT: Op = "Lt"; break;
      case BO_LE: Op = "Le"; break;
      case BO_GT: Op = "Gt"; break;
      case BO_GE: Op = "Ge"; break;
      case BO_EQ: Op = "Eq"; break;
      case BO_NE: Op = "Ne"; break;
      case BO_LAnd: Op = "And"; break;
      case BO_LOr: Op = "Or"; break;
      default: break;
      }
      // A comparison with a pointer operand. Only the test of a pointer to const against nullptr has a rule, decisions 0140 and 0141: two pointers compare
      // addresses, and the model has none. `this` has no rule either.
      if (Binary->isComparisonOp() && (Binary->getLHS()->IgnoreParenImpCasts()->getType()->isPointerType() || Binary->getRHS()->IgnoreParenImpCasts()->getType()->isPointerType())) {
        const bool NullRight = isa<CXXNullPtrLiteralExpr>(Binary->getRHS()->IgnoreParenImpCasts());
        const bool NullLeft = isa<CXXNullPtrLiteralExpr>(Binary->getLHS()->IgnoreParenImpCasts());
        const Expr *Pointer = (NullRight ? Binary->getLHS() : Binary->getRHS())->IgnoreParenImpCasts();
        if ((Binary->getOpcode() == BO_EQ || Binary->getOpcode() == BO_NE) && NullRight != NullLeft && !isa<CXXThisExpr>(Pointer) && !constPointee(Pointer->getType()).isNull())
          return tag("Bin", NullRight ? llvm::json::Array{Op, expr(Pointer, Near), "Nullopt"} : llvm::json::Array{Op, "Nullopt", expr(Pointer, Near)});
        return unknown(E, describe(E), Near);
      }
      // Division and remainder of integers carry the type of their result, decision 0088. Division of a double carries `F64`, and the core refuses it as
      // a rounding, decision 0150. Any other floating point stays unknown.
      if (!Op && (Binary->getOpcode() == BO_Div || Binary->getOpcode() == BO_Rem) && (Binary->getType()->isIntegerType() || isDouble(Binary->getType())))
        return tag("Divide", llvm::json::Array{Binary->getOpcode() == BO_Div ? "Div" : "Rem", expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near),
                                               type(Binary->getType())});
      // Two values of an enum are compared for equality only, decision 0109.
      if (Op && StringRef(Op) != "Eq" && StringRef(Op) != "Ne" && plainEnum(Binary->getLHS()->getType()))
        return unknown(E, describe(E), Near);
      // `a & b` and `a | b` of integers carry the type of their result, decision 0175. The core refuses a signed result.
      // ponytail: two operands narrower than int promote to int, so `uint8 & uint8` is refused as signed. Upgrade: the operands'
      // unsigned type when both are narrower than int.
      if (!Op && (Binary->getOpcode() == BO_And || Binary->getOpcode() == BO_Or) && Binary->getType()->isIntegerType())
        return tag("Bits", llvm::json::Array{Binary->getOpcode() == BO_And ? "BitAnd" : "BitOr", expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near), type(Binary->getType())});
      // A right shift carries the type of its result, decision 0106. A left shift has no rule.
      if (!Op && Binary->getOpcode() == BO_Shr)
        return tag("Shr", llvm::json::Array{expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near), type(Binary->getType())});
      if (!Op)
        return unknown(E, describe(E), Near);
      return tag("Bin", llvm::json::Array{Op, expr(Binary->getLHS(), Near), expr(Binary->getRHS(), Near)});
    }
    if (const auto *Unary = dyn_cast<UnaryOperator>(E)) {
      // `x++`, `x--`, `++x` and `--x` inside an expression, on a target of a write, decision 0177: the name, its type, the direction and the prefix.
      if (Unary->isIncrementDecrementOp())
        if (const auto *Target = dyn_cast<DeclRefExpr>(Unary->getSubExpr()); Target && isTarget(Target->getDecl()))
          return tag("Step", llvm::json::Array{nameOf(Target->getDecl()), varType(Target->getDecl()), Unary->isIncrementOp(), Unary->isPrefix()});
      // `*p` of a pointer to const reads the value behind the pointer, and `&x` of a variable of a scalar or a plain struct is that value as an optional,
      // decision 0140.
      if (Unary->getOpcode() == UO_Deref)
        if (const Expr *Sub = Unary->getSubExpr()->IgnoreParenImpCasts(); !isa<CXXThisExpr>(Sub) && !constPointee(Sub->getType()).isNull())
          return tag("Value", expr(Sub, Near));
      if (Unary->getOpcode() == UO_AddrOf)
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Unary->getSubExpr()->IgnoreParens()); Ref && isVariable(Ref->getDecl()) && mutRef(Ref->getDecl()->getType()).getAsNull() &&
                                                                                          !Ref->getDecl()->getType()->isReferenceType() &&
                                                                                          (scalar(Ref->getType().getUnqualifiedType()) || plainStruct(Ref->getType())))
          return tag("Wrap", expr(Ref, Near));
      if (Unary->getOpcode() == UO_LNot)
        return tag("Not", expr(Unary->getSubExpr(), Near));
      if (Unary->getOpcode() == UO_Minus)
        return tag("Neg", expr(Unary->getSubExpr(), Near));
      return unknown(E, describe(E), Near);
    }
    // `std::chrono::milliseconds{n}` is `n` as an int64, and a copy of one is the value, decision 0175.
    {
      const Expr *Built = E;
      if (const auto *Cast = dyn_cast<CXXFunctionalCastExpr>(E); Cast && Cast->getCastKind() == CK_ConstructorConversion)
        Built = Cast->getSubExpr()->IgnoreParens();
      if (const auto *Construct = dyn_cast<CXXConstructExpr>(Built); Construct && Construct->getNumArgs() == 1 && isMillis(Construct->getType())) {
        const Expr *Arg = Construct->getArg(0);
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        if (isMillis(Arg->getType()))
          return expr(Arg, Near);
        const QualType From = Arg->getType().getUnqualifiedType();
        const char *Count = scalar(From) ? scalar(From) : smallScalar(From);
        if (Count && StringRef(Count) != "Bool")
          return StringRef(Count) == "I64" ? expr(Arg, Near) : tag("Cast", llvm::json::Array{tag("Integral", llvm::json::Array{type(From), "I64"}), expr(Arg, Near)});
      }
    }
    // `a.count()` of a duration in milliseconds is `a`, and the sum of two is the sum of the counts, decision 0175.
    if (const auto *Count = dyn_cast<CXXMemberCallExpr>(E); Count && Count->getNumArgs() == 0 && Count->getMethodDecl() && Count->getMethodDecl()->getNameAsString() == "count")
      if (const Expr *Object = Count->getImplicitObjectArgument(); Object && isMillis(Object->getType()))
        return expr(Object->IgnoreParenImpCasts(), Near);
    if (const auto *Sum = dyn_cast<CXXOperatorCallExpr>(E); Sum && Sum->getOperator() == OO_Plus && Sum->getNumArgs() == 2 && isMillis(Sum->getType()) &&
                                                             isMillis(Sum->getArg(0)->getType()) && isMillis(Sum->getArg(1)->getType()))
      return tag("Bin", llvm::json::Array{"Add", expr(Sum->getArg(0)->IgnoreParenImpCasts(), Near), expr(Sum->getArg(1)->IgnoreParenImpCasts(), Near)});
    // A use of a free operator function of the file is a call of it, decision 0175. A member operator and a library operator keep their refusal.
    if (const auto *Use = dyn_cast<CXXOperatorCallExpr>(E); Use && Use->getDirectCallee() && !isa<CXXMethodDecl>(Use->getDirectCallee()) &&
                                                             freeOperator(Use->getOperator()) && !SM.isInSystemHeader(Use->getDirectCallee()->getLocation())) {
      llvm::json::Array Args;
      for (const Expr *Arg : Use->arguments())
        Args.push_back(expr(Arg, line(E->getBeginLoc())));
      return tag("Call", llvm::json::Array{key(Use->getDirectCallee()), name(Use->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
    }
    // `{a, b, c}` of a std::array is the list of its values, decision 0175. The braces of the member array inside are looked through.
    if (const auto *List = dyn_cast<InitListExpr>(E); List && isStdArray(List->getType()) && isSeq(List->getType())) {
      const InitListExpr *Values = List;
      if (List->getNumInits() == 1)
        if (const auto *Inner = dyn_cast<InitListExpr>(List->getInit(0)); Inner && Inner->getType()->isArrayType())
          Values = Inner;
      llvm::json::Array Items;
      for (const Expr *Init : Values->inits())
        Items.push_back(expr(Init, Near));
      return tag("List", std::move(Items));
    }
    // A call of a value constructor, `S s(a)`, `S s{a}`, `S(a)` and `return S(a)`, is a call of it, decision 0094. The functional cast of
    // one argument wraps the construction, and the call stands for both.
    {
      const Expr *Built = E;
      if (const auto *Cast = dyn_cast<CXXFunctionalCastExpr>(E); Cast && Cast->getCastKind() == CK_ConstructorConversion)
        Built = Cast->getSubExpr()->IgnoreParens();
      if (const auto *Construct = dyn_cast<CXXConstructExpr>(Built); Construct && valueConstructor(Construct->getConstructor())) {
        llvm::json::Array Args;
        for (unsigned I = 0; I < Construct->getNumArgs(); ++I)
          Args.push_back(callArg(Construct->getConstructor(), I, Construct->getArg(I), line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Construct->getConstructor()), name(Construct->getConstructor()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    }
    if (const auto *Cast = dyn_cast<CastExpr>(E)) {
      // `nullptr` as an argument for a pointer to const is no value, decision 0140.
      if (Cast->getCastKind() == CK_NullToPointer && isa<CXXNullPtrLiteralExpr>(Cast->getSubExpr()->IgnoreParens()))
        return "Nullopt";
      // A final class at a reference of its interface that is not const has no rule: the model has no way back from a value of the interface, decision 0169.
      if (Cast->getCastKind() == CK_DerivedToBase && !Cast->getType().isConstQualified() && Cast->getValueKind() == VK_LValue && !upcastKind(Cast).getAsNull())
        return unknown(E, "a class as a reference to its interface", Near);
      llvm::json::Value Kind = Cast->getCastKind() == CK_LValueToRValue ? llvm::json::Value("Read")
                               : Cast->getCastKind() == CK_NoOp         ? llvm::json::Value("NoOp")
                               : Cast->getCastKind() == CK_ConstructorConversion ? llvm::json::Value("Construct")
                               : Cast->getCastKind() == CK_IntegralCast && !plainEnum(Cast->getSubExpr()->getType()) && !plainEnum(Cast->getType()) ? tag("Integral", llvm::json::Array{type(Cast->getSubExpr()->getType()), type(Cast->getType())})
                               // An integer scalar to a double, decision 0159. A bool and an enum are no integer here, and a double to an integer stays `Other`.
                               // An enum is no scalar here.
                               : Cast->getCastKind() == CK_IntegralToFloating && isDouble(Cast->getType()) &&
                                     (scalar(Cast->getSubExpr()->getType().getUnqualifiedType()) || smallScalar(Cast->getSubExpr()->getType().getUnqualifiedType())) &&
                                     !Cast->getSubExpr()->getType()->isBooleanType()
                                   ? tag("Integral", llvm::json::Array{type(Cast->getSubExpr()->getType().getUnqualifiedType()), type(Cast->getType())})
                               // A final class over an interface to that interface, decision 0166. Any other derived-to-base cast stays `Other`.
                               : Cast->getCastKind() == CK_DerivedToBase && !upcastKind(Cast).getAsNull() ? upcastKind(Cast)
                                                                        : tag("Other", std::string(Cast->getStmtClassName()) + " " + Cast->getCastKindName());
      return tag("Cast", llvm::json::Array{std::move(Kind), expr(Cast->getSubExpr(), Near)});
    }
    if (const auto *Paren = dyn_cast<ParenExpr>(E))
      return tag("Paren", expr(Paren->getSubExpr(), Near));
    // `c ? a : b`, decision 0098. The GNU form `c ?: b` stays unknown.
    if (const auto *Choice = dyn_cast<ConditionalOperator>(E))
      return tag("Cond", llvm::json::Array{expr(Choice->getCond(), Near), expr(Choice->getTrueExpr(), Near), expr(Choice->getFalseExpr(), Near)});
    // A local vector made from a sequence in scope is a copy, decision 0160: a parameter or another local vector. A copy from any other expression, a call or
    // a list, stays unknown, and the core refuses the local.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && !localVec(Construct->getType()).isNull()) {
      const auto *Source = dyn_cast<DeclRefExpr>(Construct->getArg(0)->IgnoreParenImpCasts());
      const auto *Named = Source ? dyn_cast<VarDecl>(Source->getDecl()) : nullptr;
      if (Named && (isSeq(Source->getType()) || isMutSeq(Source)) && (isa<ParmVarDecl>(Named) || Named->hasLocalStorage()))
      {
        // The core judges a copy of a sequence by two `Seq` types. A vector the function writes is a dynamic sequence of its element.
        const QualType Written = isa<ParmVarDecl>(Named) ? sourceVec(Named) : localVec(Named->getType());
        llvm::json::Value From = !Written.isNull() ? tag("Seq", llvm::json::Array{elementType(Written), nullptr}) : type(Source->getType());
        return tag("Copy", llvm::json::Array{expr(Source, Near), std::move(From), tag("Seq", llvm::json::Array{elementType(localVec(Construct->getType())), nullptr})});
      }
    }
    // `std::vector<T> v;` with no initial value is the empty sequence, decision 0170.
    if (const auto *Default = dyn_cast<CXXConstructExpr>(E); Default && Default->getNumArgs() == 0 && Default->getConstructor()->isDefaultConstructor() && !localVec(Default->getType()).isNull())
      return "EmptyVec";
    // `const D d;` of a plain struct with no field and no constructor of its own is the value `S_D()`, decision 0166.
    if (const auto *Default = dyn_cast<CXXConstructExpr>(E); Default && Default->getNumArgs() == 0 && Default->getConstructor()->isDefaultConstructor()) {
      const CXXRecordDecl *RD = plainStruct(Default->getType());
      if (RD && RD->field_empty() && !RD->hasUserDeclaredConstructor())
        return tag("Construct", llvm::json::Array{structKey(RD), llvm::json::Array{}});
    }
    // A copy of a struct with a destructor is the name, so the core refuses it as a copy, decision 0178.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && plainStruct(Construct->getType()) &&
                                                               plainStruct(Construct->getArg(0)->getType()) && plainStruct(Construct->getType())->hasUserDeclaredDestructor())
      return expr(Construct->getArg(0), Near);
    // A copy or a move by a constructor that the file writes runs code that the model cannot see, decision 0179. One that the model can call was a call above.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && plainStruct(Construct->getType()) &&
                                                               Construct->getConstructor()->isCopyOrMoveConstructor() && Construct->getConstructor()->isUserProvided())
      return unknown(E, "a copy or a move by a constructor that the model cannot call", Near);
    // A sequence made from one sequence, decision 0070, or a struct made from one struct, decision 0073. The core judges the two types.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E);
        Construct && Construct->getNumArgs() == 1 &&
        ((isSeq(Construct->getType()) && isSeq(Construct->getArg(0)->getType())) ||
         (plainStruct(Construct->getType()) && plainStruct(Construct->getArg(0)->getType()))))
      return tag("Copy", llvm::json::Array{expr(Construct->getArg(0), Near), type(Construct->getArg(0)->getType()), type(Construct->getType())});
    // An optional of a scalar, decision 0075: `std::nullopt`, a value that the compiler turns into one, and a copy of one. The core
    // judges the two types of the copy. A construction from any other argument stays unknown.
    if (const auto *Construct = dyn_cast<CXXConstructExpr>(E); Construct && Construct->getNumArgs() == 1 && isOpt(Construct->getType())) {
      const Expr *Arg = Construct->getArg(0);
      const QualType From = Arg->getType().getNonReferenceType().getUnqualifiedType().getCanonicalType();
      const CXXRecordDecl *Tag = From->getAsCXXRecordDecl();
      if (Tag && Tag->isInStdNamespace() && Tag->getName() == "nullopt_t") {
        // Only the variable `std::nullopt` itself is `None`, through its implicit casts, parentheses and copies. Any other expression
        // of the type may hold a call or a read, so it stays an unknown construct.
        const Expr *Name = Arg->IgnoreParenImpCasts();
        while (const auto *Copy = dyn_cast<CXXConstructExpr>(Name)) {
          if (Copy->getNumArgs() != 1)
            break;
          Name = Copy->getArg(0)->IgnoreParenImpCasts();
        }
        if (const auto *Ref = dyn_cast<DeclRefExpr>(Name); Ref && isa<VarDecl>(Ref->getDecl()) && Ref->getDecl()->isInStdNamespace() &&
                                                           Ref->getDecl()->getName() == "nullopt")
          return "Nullopt";
        return unknown(E, E->getStmtClassName(), Near);
      }
      if (isOpt(Arg->getType()))
        return tag("Copy", llvm::json::Array{expr(Arg, Near), type(Arg->getType()), type(Construct->getType())});
      if (From == optType(Construct->getType()).getCanonicalType()) {
        // A computed value, `x + 1`, is held in a temporary for the reference parameter of the constructor. The temporary is not the value.
        if (const auto *Temporary = dyn_cast<MaterializeTemporaryExpr>(Arg))
          Arg = Temporary->getSubExpr();
        return tag("Wrap", expr(Arg, Near));
      }
    }
    // `o.has_value()` and `o.value()`.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl())
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isOpt(Object->getType())) {
        const std::string Method = Member->getMethodDecl()->getNameAsString();
        if (Method == "has_value")
          return tag("HasValue", expr(optObject(Object), Near));
        if (Method == "value")
          return tag("Value", expr(optObject(Object), Near));
      }
    // `*o`, and `*p` of a `unique_ptr`, decision 0142.
    if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(E); Operator && Operator->getOperator() == OO_Star && Operator->getNumArgs() == 1 &&
                                                                  (isOpt(Operator->getArg(0)->getType()) || isOwn(Operator->getArg(0)->getType())))
      return tag("Value", expr(optObject(Operator->getArg(0)), Near));
    if (const auto *List = dyn_cast<InitListExpr>(E); List && List->getNumInits() == 1 && List->getType()->isScalarType())
      return tag("Brace", expr(List->getInit(0), Near));
    // A braced value of a plain struct. A field that the list leaves out is an `ImplicitValueInitExpr`, which stays unknown.
    if (const auto *List = dyn_cast<InitListExpr>(E); List && plainStruct(List->getType())) {
      llvm::json::Array Args;
      for (const Expr *Init : List->inits())
        Args.push_back(expr(Init, Near));
      type(List->getType());  // writes the struct
      return tag("Construct", llvm::json::Array{structKey(plainStruct(List->getType())), std::move(Args)});
    }
    // The object of a const member function, decision 0089.
    if (const auto *This = dyn_cast<CXXThisExpr>(E); This && plainStruct(This->getType()->getPointeeType()))
      return tag("Var", llvm::json::Array{"this", thisType(This->getType()->getPointeeType()->getAsCXXRecordDecl(), !This->getType()->getPointeeType().isConstQualified())});
    // `p->f` on a pointer to const of a plain struct reads the field of its value, decision 0140.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && Member->isArrow())
      if (const Expr *Base = Member->getBase()->IgnoreParenImpCasts(); !isa<CXXThisExpr>(Base) && !constPointee(Base->getType()).isNull())
        if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
          return tag("Field", llvm::json::Array{tag("Value", expr(Base, Near)), Field->getNameAsString()});
    // `o->f` on an optional of a plain struct reads the field of its value, decision 0137. `p->f` on a `unique_ptr`, decision 0142.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && Member->isArrow())
      if (const auto *Arrow = dyn_cast<CXXOperatorCallExpr>(Member->getBase()->IgnoreParenImpCasts());
          Arrow && Arrow->getOperator() == OO_Arrow && Arrow->getNumArgs() == 1 && (isOpt(Arrow->getArg(0)->getType()) || isOwn(Arrow->getArg(0)->getType())))
        if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
          return tag("Field", llvm::json::Array{tag("Value", expr(optObject(Arrow->getArg(0)), Near)), Field->getNameAsString()});
    // A read of a field of a plain struct, also through `this`.
    if (const auto *Member = dyn_cast<MemberExpr>(E); Member && (!Member->isArrow() || isa<CXXThisExpr>(Member->getBase()->IgnoreParenImpCasts())))
      if (const auto *Field = dyn_cast<FieldDecl>(Member->getMemberDecl()); Field && plainStruct(Context.getRecordType(Field->getParent())))
        return tag("Field", llvm::json::Array{expr(Member->getBase()->IgnoreParenImpCasts(), Near), Field->getNameAsString()});
    // `v.size()` and `v[i]` of a read-only sequence.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "size")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && (isSeq(Object->getType()) || isMutSeq(Object) || isFieldVec(Object)))
        return tag("Size", expr(Object, Near));
    // `v.back()` of a vector, in code, decision 0191.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getDeclName().isIdentifier() &&
                                                             Member->getMethodDecl()->getName() == "back")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && (isSeq(Object->getType()) || isMutSeq(Object) || isFieldVec(Object)))
        return tag("Back", expr(Object, Near));
    // `v.empty()`, and `s.subspan(k)` with no explicit second argument, decision 0078. `subspan(k, n)` and `first(n)` stay unknown.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 0 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "empty")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isSeq(Object->getType()))
        return tag("Empty", expr(Object, Near));
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 2 && isa<CXXDefaultArgExpr>(Member->getArg(1)) &&
                                                             Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "subspan")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && isSeq(Object->getType()))
        return tag("Subspan", llvm::json::Array{expr(Object, Near), expr(Member->getArg(0), Near)});
    if (const auto *Operator = dyn_cast<CXXOperatorCallExpr>(E); Operator && Operator->getOperator() == OO_Subscript && Operator->getNumArgs() == 2 &&
                                                                  (isSeq(Operator->getArg(0)->getType()) || isMutSeq(Operator->getArg(0)) || isFieldVec(Operator->getArg(0))))
      return tag("Index", llvm::json::Array{expr(Operator->getArg(0), Near), expr(Operator->getArg(1), Near)});
    // `v.at(i)` of a read-only sequence is `v[i]`, decision 0139. The prover proves the index in range, so `at` never throws.
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E); Member && Member->getNumArgs() == 1 && Member->getMethodDecl() && Member->getMethodDecl()->getNameAsString() == "at")
      if (const Expr *Object = Member->getImplicitObjectArgument(); Object && (isSeq(Object->getType()) || isFieldVec(Object)))
        return tag("Index", llvm::json::Array{expr(Object, Near), expr(Member->getArg(0), Near)});
    // `p->f(a)` on a unique_ptr of an interface is a call of the function of the interface on the value of `p`, decision 0168.
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(E); Call && Call->getDirectCallee() && ifaceMethod(Call->getDirectCallee()))
      if (const auto *Arrow = dyn_cast<CXXOperatorCallExpr>(Call->getImplicitObjectArgument()->IgnoreParenImpCasts());
          Arrow && Arrow->getOperator() == OO_Arrow && Arrow->getNumArgs() == 1 && isOwn(Arrow->getArg(0)->getType())) {
        const auto *Callee = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
        if (Callee && Callee->hasQualifier())
          return unknown(E, "a qualified call of a virtual function", Near);
        // A call that writes the object names the variable, with no cast, so the core finds the unique_ptr that takes the new value, decision 0169.
        // So does the element of a vector of unique_ptr, `v[i]->f(a)`, decision 0170.
        const Expr *Bare = Arrow->getArg(0)->IgnoreParenImpCasts();
        const auto *Element = dyn_cast<CXXOperatorCallExpr>(Bare);
        const Expr *Pointer = Call->getMethodDecl()->isConst() || !(isa<DeclRefExpr>(Bare) || (Element && Element->getOperator() == OO_Subscript)) ? optObject(Arrow->getArg(0)) : Bare;
        llvm::json::Array Args{tag("Value", expr(Pointer, line(E->getBeginLoc())))};
        for (const Expr *Arg : Call->arguments())
          Args.push_back(expr(Arg, line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    // A call of a member function, `o.f(a)` or `f(a)` in a method, is a call of `f` with the object first, decisions 0089 and 0096.
    if (const auto *Call = dyn_cast<CXXMemberCallExpr>(E); Call && Call->getDirectCallee() && member(Call->getDirectCallee())) {
      const Expr *Object = Call->getImplicitObjectArgument()->IgnoreParenImpCasts();
      const auto *Callee = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
      // A call of a virtual function with the name of its class runs that function, not an override, decision 0165.
      if (Callee && Callee->hasQualifier() && Call->getMethodDecl() && Call->getMethodDecl()->isVirtual())
        return unknown(E, "a qualified call of a virtual function", Near);
      if (Callee && (!Callee->isArrow() || isa<CXXThisExpr>(Object))) {
        // The object can be a chain of calls that give back their object, decision 0183.
        const CXXMemberCallExpr *Chain = fluentCall(Object);
        llvm::json::Array Args{Chain ? (E == HoistOk ? chain(Chain, line(HoistFor->getBeginLoc()), false) : nested(Chain, line(E->getBeginLoc()))) : expr(Object, line(E->getBeginLoc()))};
        for (unsigned I = 0; I < Call->getNumArgs(); ++I)
          Args.push_back(callArg(Call->getDirectCallee(), I, Call->getArg(I), line(E->getBeginLoc())));
        return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
      }
    }
    // A call of an object, `c(x)`, is a call of its `operator()` with the object first, decision 0098.
    if (const auto *Call = dyn_cast<CXXOperatorCallExpr>(E); Call && Call->getOperator() == OO_Call && Call->getNumArgs() >= 1 && Call->getDirectCallee() &&
                                                             member(Call->getDirectCallee())) {
      llvm::json::Array Args{expr(Call->getArg(0)->IgnoreParenImpCasts(), line(E->getBeginLoc()))};
      for (unsigned I = 1; I < Call->getNumArgs(); ++I)
        Args.push_back(expr(Call->getArg(I), line(E->getBeginLoc())));
      return tag("Call", llvm::json::Array{key(Call->getDirectCallee()), name(Call->getDirectCallee()), std::move(Args), number(line(E->getBeginLoc()))});
    }
    // `std::count_if(v.begin(), v.end(), [captures](T x) { return e; })` over a sequence parameter, decision 0149. The captures are by copy and the
    // body is one `return`. Anything else stays a call, which has no model, and is refused.
    std::string Limit;
    if (const llvm::json::Value Counted = countIf(E, Near, Limit); !Counted.getAsNull())
      return Counted;
    // A count_if that misses a limit names it, decision 0157.
    if (!Limit.empty())
      return unknown(E, Limit, Near);
    // Only a plain call by name. A member call, an operator call and the rest of the call classes stay unknown.
    if (E->getStmtClass() == Stmt::CallExprClass)
      if (const FunctionDecl *Callee = cast<CallExpr>(E)->getDirectCallee()) {
        llvm::json::Array Args;
        for (unsigned I = 0; I < cast<CallExpr>(E)->getNumArgs(); ++I) {
          const Expr *Arg = cast<CallExpr>(E)->getArg(I);
          // A class at a reference of its interface that is not const stands for the whole call, because the core would refuse the write-back first, decision 0169.
          if (const auto *Up = dyn_cast<ImplicitCastExpr>(Arg->IgnoreParens()); Up && Up->getCastKind() == CK_DerivedToBase && !Up->getType().isConstQualified() &&
                                                                              Up->getValueKind() == VK_LValue && !upcastKind(Up).getAsNull())
            return unknown(E, "a class as a reference to its interface", Near);
          Args.push_back(callArg(Callee, I, Arg, line(E->getBeginLoc())));
        }
        return tag("Call", llvm::json::Array{key(Callee), name(Callee), std::move(Args), number(line(E->getBeginLoc()))});
      }
    return unknown(E, E->getStmtClassName(), Near);
  }
};

// Everything in view is accounted for. Each function that a non-system file defines is written, and each `//@` line of such a file that
// no function claimed is written as `{"orphan": line, "file": name}`. A deleted function runs nothing, so it is not written, and it
// claims no line.
// ponytail: the orphan scan reads the text, not the tokens. A line that holds `//@` anywhere is an orphan when nothing claimed it, and
// only a line that starts with `//@` can be claimed. So a `//@` after code, in a block comment or in a raw string is an orphan too,
// which only refuses more. Upgrade: the lexer's comment tokens.
class TreeCheck : public ClangTidyCheck {
public:
  TreeCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Output(Options.get("Output", "")) {}
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(
        functionDecl(unless(isImplicit()), unless(isExpansionInSystemHeader())).bind("fn"), this);
    Finder->addMatcher(varDecl(isConstexpr(), unless(isExpansionInSystemHeader())).bind("constant"), this);
    Finder->addMatcher(varDecl(hasGlobalStorage(), unless(isConstexpr()), unless(isExpansionInSystemHeader())).bind("global"), this);
    Finder->addMatcher(enumDecl(isDefinition(), unless(isExpansionInSystemHeader())).bind("enum"), this);
    Finder->addMatcher(cxxRecordDecl(isDefinition(), unless(isImplicit()), unless(isExpansionInSystemHeader())).bind("class"), this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    Context = Result.Context;
    // The named constants of the file, decision 0106. A contract reads them by name.
    if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("constant")) {
      llvm::json::Value Line = TreeWriter(*Context, Claimed, Structs).constantLine(Var);
      if (Line.kind() != llvm::json::Value::Null)
        append(Line);
      return;
    }
    // The mutable globals and static data members of the file, in the order of their definitions, decision 0173.
    if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("global")) {
      llvm::json::Value Line = TreeWriter(*Context, Claimed, Structs).globalLine(Var);
      if (Line.kind() != llvm::json::Value::Null)
        append(Line);
      return;
    }
    // Each enum class of the file is written, whether or not a type names it, decision 0114.
    if (const auto *ED = Result.Nodes.getNodeAs<EnumDecl>("enum")) {
      TreeWriter(*Context, Claimed, Structs).writeEnum(ED);
      return;
    }
    // A class over interfaces is written in the table of structs for its line, decision 0165.
    if (const auto *RD = Result.Nodes.getNodeAs<CXXRecordDecl>("class")) {
      TreeWriter Writer(*Context, Claimed, Structs);
      // A class template with no instance is refused at its class. An instance of one is a struct of the model, whether or not a type names it, decision 0188.
      Writer.refuseUnnamedInstances(RD);
      if (Writer.noInstanceClass(RD))
        append(Writer.noInstanceEntry(RD->getName(), Writer.structKey(RD), RD->getLocation(), "a class template with no instance"));
      else if (Writer.classInstance(RD))
        (void)Writer.type(Context->getRecordType(RD));
      TreeWriter(*Context, Claimed, Structs).classEntry(RD);
      TreeWriter(*Context, Claimed, Structs).staticEntry(RD);
      TreeWriter(*Context, Claimed, Structs).holderEntry(RD);
      return;
    }
    const auto *FD = Result.Nodes.getNodeAs<FunctionDecl>("fn");
    // A defaulted destructor has no contract and no body, so it is no member of the model, decision 0178.
    if (!FD || FD->isDeleted() || (isa<CXXDestructorDecl>(FD) && FD->isDefaulted() && !TreeWriter::outOfLineDefault(FD)))
      return;
    // The call operator of a lambda is no function of its own, decision 0149. The call that takes the lambda reads its body, or is refused.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(FD); Method && Method->getParent()->isLambda())
      return;
    const TreeWriter Reader(*Context, Claimed, Structs);
    // An instance of a function template is a function of the model, decision 0180. So is a member function of an instance of a class template, decision 0188.
    // Any other instance is the template, which is refused once.
    if (FD->isTemplateInstantiation() && !Reader.instanceMember(FD) &&
        !(FD->getPrimaryTemplate() && TreeWriter::typeOnlyTemplate(FD->getPrimaryTemplate()) && FD->isThisDeclarationADefinition()))
      return;
    const Contract C = contractOf(Context->getSourceManager(), FD);
    for (const Contract::Line &L : C.Lines)
      Claimed.insert({L.File, L.Number});
    // The member function of a class template is written for each instance and not alone, decision 0188. The class is refused where it has no instance.
    if (Reader.inClassTemplate(FD)) {
      if (FD->getBody())
        TreeWriter(*Context, Claimed, Structs).claimBody(FD);
      // A member function with a contract that no instance makes is refused at its line. A class with no instance is refused at its class.
      const CXXRecordDecl *Parent = cast<CXXMethodDecl>(FD)->getParent();
      if (FD->isThisDeclarationADefinition() && !C.Lines.empty() && !Reader.noInstanceClass(Parent) && !Reader.memberHasInstance(FD))
        append(Reader.noInstanceEntry(FD->getNameAsString(), Reader.key(FD), FD->getLocation(), "a member function with no instance"));
      return;
    }
    // A member function of an instance that has no body here has no model. A contract that calls it is refused, decision 0188.
    if (Reader.instanceMember(FD) && !FD->isThisDeclarationADefinition())
      return;
    // The template itself is written for each instance and not alone. One with no instance has no model, decision 0180.
    if (TreeWriter::typeOnlyTemplate(FD->getDescribedFunctionTemplate())) {
      if (FD->getBody())
        TreeWriter(*Context, Claimed, Structs).claimBody(FD);
      // One with no instance in the main file is refused at its line.
      if (!TreeWriter::noInstance(FD))
        return;
    }
    // The member functions of a class over an interface that is not final, and the defaulted destructor of an interface, are left out, decision 0165.
    if (TreeWriter(*Context, Claimed, Structs).leftOut(FD))
      return;
    // A trusted function with no definition here is written once, at its first declaration. Its contract lines come from all of them.
    // ponytail: a trusted template is not written. A trusted constructor with no body here is written and refused as CXXConstructorDecl, and
    // one with a body is refused by valueConstructor unless its body is empty and it gives each field a value. Upgrade: their signatures.
    if (FD->isThisDeclarationADefinition() || (TreeWriter(*Context, Claimed, Structs).ifaceMethod(FD) && !FD->getDefinition()) ||
        (!FD->getDefinition() && FD == FD->getCanonicalDecl() && !FD->isTemplated() && trustedReason(FD)))
      append(TreeWriter(*Context, Claimed, Structs).function(FD, C));
  }
  void onEndOfTranslationUnit() override {
    if (!Context)
      return;
    const SourceManager &SM = Context->getSourceManager();
    for (const auto &[Key, Line] : Structs)
      append(Line);
    for (unsigned I = 0; I < SM.local_sloc_entry_size(); ++I) {
      const SrcMgr::SLocEntry &Entry = SM.getLocalSLocEntry(I);
      if (!Entry.isFile())
        continue;
      const SourceLocation Start = SourceLocation::getFromRawEncoding(Entry.getOffset());
      const FileID ID = SM.getFileID(Start);
      // The compiler's own buffers, such as the predefined macros, are no file.
      if (!SM.getFileEntryForID(ID) || SM.isInSystemHeader(Start))
        continue;
      unsigned Number = 0;
      for (StringRef Rest = SM.getBufferData(ID); !Rest.empty();) {
        const auto [Line, Tail] = Rest.split('\n');
        ++Number;
        Rest = Tail;
        if (Line.contains("//@") && !Claimed.count({ID.getHashValue(), Number}))
          append(llvm::json::Object{{"orphan", static_cast<int64_t>(Number)}, {"file", SM.getFilename(Start).str()}, {"word", orphanWord(Line)}});
      }
    }
  }

private:
  // The word of a line that starts with `//@`, else empty. The translator says more for an assert or apply line, decision 0099.
  static std::string orphanWord(StringRef Line) {
    Line = Line.trim();
    if (!Line.consume_front("//@"))
      return "";
    Line = Line.ltrim();
    return Line.substr(0, Line.find_first_of(" \t\f\v\r")).str();
  }

  std::string Output;
  ASTContext *Context = nullptr;
  std::set<std::pair<unsigned, unsigned>> Claimed;
  std::map<std::string, llvm::json::Value> Structs;  // each plain struct that a function names, by key

  void append(const llvm::json::Value &V) {
    std::error_code EC;
    llvm::raw_fd_ostream OS(Output, EC, llvm::sys::fs::OF_Append | llvm::sys::fs::OF_Text);
    if (EC) {
      configurationDiag("cplusp-tree cannot write %0: %1") << Output << EC.message();
      return;
    }
    OS << llvm::formatv("{0}", V) << "\n";
  }
};
} // namespace

void addTreeCheck(ClangTidyCheckFactories &Factories) {
    Factories.registerCheck<TreeCheck>("cplusp-tree");
}

} // namespace cplusp::detail
