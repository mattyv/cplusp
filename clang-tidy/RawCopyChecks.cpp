#include "CplusPChecks.h"

namespace cplusp::detail {

namespace {
// ---------------------------------------------------------------- cplusp-raw-copy, decisions 0116 to 0120: the row type_punning
// A raw copy of bytes can make a value that its type does not have. The check judges a bit cast, memcpy, memmove, memset and a cast to non-const bytes.

// The std::byte of the system header. It holds no bad value, and it is a view as bytes. A std::byte that the file declares is an enum like any other.
bool isSystemByte(QualType T, const SourceManager &SM) {
  const auto *Enum = dyn_cast<EnumType>(T.getCanonicalType().getTypePtr());
  const EnumDecl *Decl = Enum ? Enum->getDecl() : nullptr;
  return Decl && Decl->getName() == "byte" && Decl->getDeclContext()->isStdNamespace() && SM.isInSystemHeader(Decl->getLocation());
}

// char, unsigned char or the std::byte of the system header, with any cv: the types that C++ lets any object be read as.
bool isByteScalar(QualType T, const SourceManager &SM) {
  T = T.getCanonicalType();
  if (isSystemByte(T, SM))
    return true;
  const auto *Builtin = dyn_cast<BuiltinType>(T.getTypePtr());
  return Builtin && (Builtin->getKind() == BuiltinType::Char_S || Builtin->getKind() == BuiltinType::Char_U || Builtin->getKind() == BuiltinType::UChar);
}

// Bytes: a byte scalar, an array of bytes, or a class that holds only bytes, such as std::array<uint8_t, 8>.
bool isBytes(QualType T, const SourceManager &SM) {
  T = T.getCanonicalType();
  if (isByteScalar(T, SM))
    return true;
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return isBytes(Array->getElementType(), SM);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || RD->isUnion())
    return false;
  RD = RD->getDefinition();
  for (const CXXBaseSpecifier &Base : RD->bases())
    if (!isBytes(Base.getType(), SM))
      return false;
  bool Any = RD->getNumBases() != 0;
  for (const FieldDecl *Field : RD->fields()) {
    if (Field->isBitField() || !isBytes(Field->getType(), SM))
      return false;
    Any = true;
  }
  return Any;
}

// Whether a type holds a bad value at some depth, decisions 0118 and 0119: a pointer, a pointer to a member, a reference, an enum other than the system
// std::byte, or a bool. The depth covers a field, a base and an element of an array. Any bit pattern of an integer or a floating type is a value.
bool holdsBadValue(QualType T, const SourceManager &SM, llvm::SmallPtrSetImpl<const CXXRecordDecl *> &Seen) {
  T = T.getCanonicalType();
  if (isSystemByte(T, SM))
    return false;
  if (T->isPointerType() || T->isMemberPointerType() || T->isReferenceType() || T->isEnumeralType() || T->isBooleanType())
    return true;
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return holdsBadValue(Array->getElementType(), SM, Seen);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || !Seen.insert(RD->getDefinition()).second)
    return false;
  RD = RD->getDefinition();
  // A class with a virtual function or a virtual base holds a hidden pointer, decision 0120.
  if (RD->isDynamicClass())
    return true;
  for (const CXXBaseSpecifier &Base : RD->bases())
    if (holdsBadValue(Base.getType(), SM, Seen))
      return true;
  for (const FieldDecl *Field : RD->fields())
    if (holdsBadValue(Field->getType(), SM, Seen))
      return true;
  return false;
}

bool holdsBadValue(QualType T, const SourceManager &SM) {
  llvm::SmallPtrSet<const CXXRecordDecl *, 8> Seen;
  return holdsBadValue(T, SM, Seen);
}

// Whether a type has padding at some depth, decision 0119: a gap between its sub-objects in the layout of the compiler, at any depth. A union has
// padding when a member is smaller than the union. A floating type that does not fill its size, such as long double, has padding.
bool hasPadding(QualType T, ASTContext &Context, llvm::SmallPtrSetImpl<const CXXRecordDecl *> &Seen) {
  T = T.getCanonicalType();
  if (const auto *Array = T->getAsArrayTypeUnsafe())
    return hasPadding(Array->getElementType(), Context, Seen);
  if (T->isFloatingType())
    return llvm::APFloat::getSizeInBits(Context.getFloatTypeSemantics(T)) < Context.getTypeSize(T);
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition() || !Seen.insert(RD->getDefinition()).second)
    return false;
  RD = RD->getDefinition();
  const ASTRecordLayout &Layout = Context.getASTRecordLayout(RD);
  const uint64_t Size = Context.toBits(Layout.getSize());
  // The sub-objects as ranges of bits.
  std::vector<std::pair<uint64_t, uint64_t>> Ranges;
  for (const CXXBaseSpecifier &Base : RD->bases()) {
    const CXXRecordDecl *BaseDecl = Base.getType()->getAsCXXRecordDecl();
    if (Base.isVirtual() || !BaseDecl)
      return true;
    // An empty base takes no bits, decision 0120.
    if (BaseDecl->isEmpty())
      continue;
    if (hasPadding(Base.getType(), Context, Seen))
      return true;
    const uint64_t At = Context.toBits(Layout.getBaseClassOffset(BaseDecl));
    Ranges.push_back({At, At + Context.getTypeSize(Base.getType())});
  }
  if (RD->isUnion()) {
    for (const FieldDecl *Field : RD->fields())
      if (hasPadding(Field->getType(), Context, Seen) || (Field->isBitField() ? Field->getBitWidthValue(Context) : Context.getTypeSize(Field->getType())) < Size)
        return true;
    return false;
  }
  for (const FieldDecl *Field : RD->fields()) {
    // A field of size zero takes no bits, decision 0120.
    if (Field->isZeroSize(Context))
      continue;
    if (hasPadding(Field->getType(), Context, Seen))
      return true;
    const uint64_t At = Layout.getFieldOffset(Field->getFieldIndex());
    Ranges.push_back({At, At + (Field->isBitField() ? Field->getBitWidthValue(Context) : Context.getTypeSize(Field->getType()))});
  }
  std::sort(Ranges.begin(), Ranges.end());
  uint64_t Covered = 0;
  for (const auto &[From, To] : Ranges) {
    if (From > Covered)
      return true;
    Covered = std::max(Covered, To);
  }
  return Covered < Size;
}

bool hasPadding(QualType T, ASTContext &Context) {
  llvm::SmallPtrSet<const CXXRecordDecl *, 8> Seen;
  return hasPadding(T, Context, Seen);
}

// cplusp-raw-copy: the row is type_punning. It reports
//  - a `std::bit_cast`, a call or its address, whose result holds a bad value, or whose source has padding when the result is not bytes;
//  - a function of the C library that copies or clears raw bytes, whose destination holds a bad value, whose source has padding when the destination is
//    not bytes, or whose destination or source has an unknown or incomplete type, such as `void*`; and the name of such a function that is not called;
//  - a cast to a pointer or a reference to non-const bytes from a pointer or an object that holds a bad value, from `void*`, from an integer, or a
//    `const_cast` that takes const from bytes;
//  - `std::as_writable_bytes` of a span whose element holds a bad value.
// A template is judged at each instance. A matcher cannot look through the fields of a type.
// ponytail: the bit casts of the library are a list kept by hand. Upgrade: match builtinBitCastExpr in the system instantiations, and report it at the
// call site in the user's file.
// ponytail: the functions of the C library are a list kept by hand. Upgrade: ask for each function with a void* parameter that the library writes through.
const char *const WritesBad = "type_punning: The copy writes a type that holds a pointer, a reference, an enum or a bool.";
const char *const ReadsPadding = "type_punning: The copy reads padding into a type that is not bytes.";
const char *const WritesUnknown = "type_punning: The copy writes to a place of unknown type.";
const char *const ReadsUnknown = "type_punning: The copy reads a place of unknown type into a type that is not bytes.";

// The functions of the C library that write or clear raw bytes, with their __builtin_ names.
const char *const RawCopyNames[] = {
    "memcpy", "memmove", "memset", "mempcpy", "memccpy", "bcopy", "bzero", "explicit_bzero",
    "__builtin_memcpy", "__builtin_memmove", "__builtin_memset", "__builtin_mempcpy", "__builtin_memccpy", "__builtin_bcopy", "__builtin_bzero",
    "__builtin___memcpy_chk", "__builtin___memmove_chk", "__builtin___memset_chk", "__builtin___mempcpy_chk",
};

class RawCopyCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override {
    Finder->addMatcher(declRefExpr(to(functionDecl(hasAnyName("::std::bit_cast", "::std::experimental::__bit_cast", "::std::experimental::__proposed::simd_bit_cast"))),
                                   unless(isExpansionInSystemHeader()))
                           .bind("bit"),
                       this);
    Finder->addMatcher(declRefExpr(to(functionDecl(hasName("::std::as_writable_bytes"))), unless(isExpansionInSystemHeader())).bind("view"), this);
    // The name of a copy function, called or not. A call is judged by its arguments, and the name that is not called fails closed.
    const std::vector<StringRef> Names(std::begin(RawCopyNames), std::end(RawCopyNames));
    Finder->addMatcher(declRefExpr(to(functionDecl(hasAnyName(Names))), unless(isExpansionInSystemHeader())).bind("name"), this);
    Finder->addMatcher(explicitCastExpr(anyOf(hasCastKind(CK_BitCast), hasCastKind(CK_LValueBitCast), hasCastKind(CK_IntegralToPointer)), unless(isExpansionInSystemHeader())).bind("cast"), this);
    Finder->addMatcher(explicitCastExpr(anyOf(cxxConstCastExpr(), cStyleCastExpr(hasCastKind(CK_NoOp)), cxxFunctionalCastExpr(hasCastKind(CK_NoOp))), unless(isExpansionInSystemHeader())).bind("unconst"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    Context = Result.Context;
    SM = Result.SourceManager;
    if (const auto *Ref = Result.Nodes.getNodeAs<DeclRefExpr>("bit"))
      bitCast(Ref);
    else if (const auto *View = Result.Nodes.getNodeAs<DeclRefExpr>("view"))
      writableBytes(View);
    else if (const auto *Name = Result.Nodes.getNodeAs<DeclRefExpr>("name"))
      named(Name);
    else if (const auto *Cast = Result.Nodes.getNodeAs<ExplicitCastExpr>("cast"))
      toBytes(Cast);
    else if (const auto *Unconst = Result.Nodes.getNodeAs<ExplicitCastExpr>("unconst"))
      unconst(Unconst);
  }

private:
  ASTContext *Context = nullptr;
  const SourceManager *SM = nullptr;

  void report(SourceLocation At, const char *Why) { diag(SM->getFileLoc(At), "%0") << Why; }

  void bitCast(const DeclRefExpr *Ref) {
    const auto *Function = dyn_cast<FunctionDecl>(Ref->getDecl());
    if (!Function || Function->getReturnType()->isDependentType())
      return;
    const QualType Result = Function->getReturnType();
    if (holdsBadValue(Result, *SM)) {
      report(Ref->getBeginLoc(), WritesBad);
      return;
    }
    if (Function->getNumParams() == 0)
      return;
    QualType From = Function->getParamDecl(0)->getType();
    if (From->isReferenceType())
      From = From->getPointeeType();
    if (!From->isDependentType() && hasPadding(From, *Context) && !isBytes(Result, *SM))
      report(Ref->getBeginLoc(), ReadsPadding);
  }

  // `std::as_writable_bytes` of a span whose element holds a bad value writes bytes into it.
  void writableBytes(const DeclRefExpr *Ref) {
    const auto *Function = dyn_cast<FunctionDecl>(Ref->getDecl());
    if (!Function || Function->getNumParams() == 0 || Function->getParamDecl(0)->getType()->isDependentType())
      return;
    const auto *Span = Function->getParamDecl(0)->getType().getCanonicalType()->getAsCXXRecordDecl();
    const auto *Special = dyn_cast_or_null<ClassTemplateSpecializationDecl>(Span);
    if (Special && Special->getTemplateArgs().size() > 0 && Special->getTemplateArgs()[0].getKind() == TemplateArgument::Type &&
        holdsBadValue(Special->getTemplateArgs()[0].getAsType(), *SM))
      report(Ref->getBeginLoc(), WritesBad);
  }

  // Whether the name is the callee of a call: its parent is the decay to a pointer, and the parent of that is the call.
  bool isCallee(const DeclRefExpr *Ref) const {
    for (const auto &Up : Context->getParents(*Ref))
      if (const auto *Decay = Up.get<ImplicitCastExpr>())
        for (const auto &Above : Context->getParents(*Decay))
          if (const auto *Call = Above.get<CallExpr>(); Call && Call->getCallee() == Decay)
            return true;
    return false;
  }

  // The name of a copy function. A call is judged by its arguments. A name that is not called fails closed.
  void named(const DeclRefExpr *Ref) {
    if (!isCallee(Ref)) {
      report(Ref->getBeginLoc(), WritesUnknown);
      return;
    }
    for (const auto &Up : Context->getParents(*Ref))
      for (const auto &Above : Context->getParents(Up))
        if (const auto *Call = Above.get<CallExpr>())
          memory(Call, cast<FunctionDecl>(Ref->getDecl()));
  }

  // The type that a pointer expression points to, before the conversion to void*, or a null type when the expression is no pointer or an array.
  QualType pointee(const Expr *E) const {
    E = E->IgnoreParenImpCasts();
    const QualType T = E->getType().getCanonicalType();
    if (T->isPointerType())
      return T->getPointeeType();
    if (T->isArrayType())
      return T;
    return QualType();
  }

  void memory(const CallExpr *Call, const FunctionDecl *Callee) {
    // The name without its prefix and suffix: __builtin___memcpy_chk is memcpy.
    StringRef Name = Callee->getName();
    Name.consume_front("__builtin___") || Name.consume_front("__builtin_");
    Name.consume_back("_chk");
    const bool Reversed = Name == "bcopy";
    const bool Copies = Name == "memcpy" || Name == "memmove" || Name == "mempcpy" || Name == "memccpy" || Reversed;
    const unsigned ToAt = Reversed ? 1 : 0, FromAt = Reversed ? 0 : 1;
    if (Call->getNumArgs() <= (Copies ? 1u : 0u) || Call->getArg(ToAt)->isTypeDependent() || (Copies && Call->getArg(FromAt)->isTypeDependent()))
      return;
    const QualType To = pointee(Call->getArg(ToAt));
    if (To.isNull() || To->isVoidType() || To->isIncompleteType()) {
      report(Call->getBeginLoc(), WritesUnknown);
      return;
    }
    if (holdsBadValue(To, *SM)) {
      report(Call->getBeginLoc(), WritesBad);
      return;
    }
    if (!Copies || isBytes(To, *SM))
      return;
    const QualType From = pointee(Call->getArg(FromAt));
    if (From.isNull() || From->isVoidType() || From->isIncompleteType())
      report(Call->getBeginLoc(), ReadsUnknown);
    else if (hasPadding(From, *Context))
      report(Call->getBeginLoc(), ReadsPadding);
  }

  // The pointer or reference type that a cast writes, as the object type, or a null type.
  QualType writtenObject(const ExplicitCastExpr *Cast) const {
    const QualType Written = Cast->getTypeAsWritten().getCanonicalType();
    return Written->isPointerType() || Written->isReferenceType() ? Written->getPointeeType() : QualType();
  }

  // The object that a cast reads: the pointee of a pointer, or the object of a reference cast. Null when the source is no pointer.
  QualType readObject(const ExplicitCastExpr *Cast) const {
    const QualType From = Cast->getSubExpr()->getType().getCanonicalType();
    if (Cast->getTypeAsWritten()->isPointerType())
      return From->isPointerType() ? From->getPointeeType() : QualType();
    return From;
  }

  void toBytes(const ExplicitCastExpr *Cast) {
    const QualType To = writtenObject(Cast);
    if (To.isNull() || To.isConstQualified() || !isByteScalar(To, *SM) || Cast->getSubExpr()->isTypeDependent())
      return;
    const QualType From = readObject(Cast);
    if (From.isNull() || From->isVoidType() || From->isIncompleteType())
      report(Cast->getBeginLoc(), WritesUnknown);
    else if (holdsBadValue(From, *SM))
      report(Cast->getBeginLoc(), WritesBad);
  }

  // A const_cast that takes const away from bytes makes a view that can write the object, which the gate cannot see.
  void unconst(const ExplicitCastExpr *Cast) {
    const QualType To = writtenObject(Cast);
    if (To.isNull() || To.isConstQualified() || !isByteScalar(To, *SM) || Cast->getSubExpr()->isTypeDependent())
      return;
    const QualType From = readObject(Cast);
    if (!From.isNull() && From.isConstQualified() && isByteScalar(From, *SM))
      report(Cast->getBeginLoc(), WritesUnknown);
  }
};

// cplusp-allowlist: decision 0032. The gate refuses every kind of node it does not know. The options are three lists of allowed kinds,
// `statements`, `declarations` and `types`, a list of allowed attributes, `attributes`, and one option per row of the policy,
// `{row}: kinds`, that names the kinds the row claims. An attribute is no node, so it has its own list and the message
// `unlisted: The attribute is {spelling}.`
// A kind names the class of the node in clang: `GotoStmt`, `ImplicitCastExpr`, `FunctionDecl`, `BuiltinType`. The message is
// `{row}: The construct is {Kind}.` A kind that a row claims is that row's finding, even when it is on a list. A kind on no row and on
// no list is `unlisted`. Like the generic check, it reads the tree as the compiler has it, with the implicit casts.
class AllowlistCheck : public ClangTidyCheck {
public:
  AllowlistCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}

  void registerMatchers(MatchFinder *Finder) override {
    const std::string Prefix = (getID() + ".").str();
    for (const auto &Option : Ctx->getOptions().CheckOptions) {
      StringRef Key = Option.getKey();
      if (!Key.consume_front(Prefix))
        continue;
      llvm::SmallVector<StringRef, 16> Kinds;
      StringRef(Option.getValue().Value).split(Kinds, ',', -1, false);
      for (StringRef Kind : Kinds) {
        Kind = Kind.trim();
        if (Kind.empty())
          continue;
        if (Key == "statements")
          Statements.insert(Kind);
        else if (Key == "declarations")
          Declarations.insert(Kind);
        else if (Key == "types")
          Types.insert(Kind);
        else if (Key == "attributes")
          Attributes.insert(Kind);
        else
          Claimed[Kind] = Key.str();
      }
    }
    // A node in a system header is no source of ours. The body of an implicit function comes from the compiler too, so none of its
    // statements is. Nor is a node below a substituted template argument: clang writes `(Enum)1` for an enum argument, and the
    // argument is judged where it is written. The test of the location comes first, because the headers hold most of the nodes.
    Finder->addMatcher(stmt(unless(isExpansionInSystemHeader()), unless(hasAncestor(functionDecl(isImplicit()))),
                            unless(hasAncestor(substNonTypeTemplateParmExpr())))
                           .bind("stmt"),
                       this);
    Finder->addMatcher(decl(unless(isExpansionInSystemHeader())).bind("decl"), this);
    Finder->addMatcher(typeLoc(unless(isExpansionInSystemHeader())).bind("type"), this);
  }

  void check(const MatchFinder::MatchResult &Result) override {
    SourceLocation Loc;
    std::string Kind;
    const llvm::StringSet<> *Allowed = nullptr;
    if (const auto *S = Result.Nodes.getNodeAs<Stmt>("stmt")) {
      if (const auto *Attributed = dyn_cast<AttributedStmt>(S))
        for (const Attr *A : Attributed->getAttrs())
          checkAttribute(A, *Result.SourceManager);
      Loc = S->getBeginLoc();
      Kind = S->getStmtClassName();
      Allowed = &Statements;
    } else if (const auto *D = Result.Nodes.getNodeAs<Decl>("decl")) {
      // The kinds of an implicit declaration come from the compiler, not from the source.
      if (D->isImplicit() || isa<TranslationUnitDecl>(D))
        return;
      // The word `friend` in a plain type is out of view, whatever the friend is. The bot cannot change the type, decision 0053.
      if (isa<FriendDecl>(D) && insidePlain(cast<Decl>(D->getLexicalDeclContext())))
        return;
      for (const Attr *A : D->attrs())
        checkAttribute(A, *Result.SourceManager);
      // A member function with `__restrict` after its parameters promises that `this` does not alias, and no type holds that qualifier.
      if (const auto *Method = dyn_cast<CXXMethodDecl>(D); Method && Method->getMethodQualifiers().hasRestrict())
        diag(Result.SourceManager->getFileLoc(D->getLocation()), "unlisted: The construct is __restrict.");
      Loc = D->getLocation();
      Kind = std::string(D->getDeclKindName()) + "Decl";
      Allowed = &Declarations;
    } else if (const auto *T = Result.Nodes.getNodeAs<TypeLoc>("type")) {
      if (T->isNull())
        return;
      Loc = T->getBeginLoc();
      Kind = std::string(T->getTypePtr()->getTypeClassName()) + "Type";
      Allowed = &Types;
      // A qualifier is no node kind and no attribute, and `__restrict` promises the compiler that two pointers never alias.
      if (T->getType().isLocalRestrictQualified() && Loc.isValid())
        diag(Result.SourceManager->getFileLoc(Loc), "unlisted: The construct is __restrict.");
    } else {
      return;
    }
    if (Loc.isInvalid())
      return;
    // A node from a macro is reported where the macro is used.
    Loc = Result.SourceManager->getFileLoc(Loc);
    const auto Row = Claimed.find(Kind);
    if (Row != Claimed.end())
      diag(Loc, "%0: The construct is %1.") << Row->second << Kind;
    else if (!Allowed->contains(Kind))
      diag(Loc, "unlisted: The construct is %0.") << Kind;
  }

private:
  ClangTidyContext *Ctx;
  llvm::StringSet<> Statements, Declarations, Types, Attributes;
  // The kind, and the row that claims it.
  llvm::StringMap<std::string> Claimed;

  // An attribute that the compiler added, or that a redeclaration inherited, is judged where it is written.
  void checkAttribute(const Attr *A, const SourceManager &SM) {
    if (A->isImplicit() || A->isInherited() || Attributes.contains(A->getSpelling()) || A->getLocation().isInvalid())
      return;
    diag(SM.getFileLoc(A->getLocation()), "unlisted: The attribute is %0.") << A->getSpelling();
  }
};

} // namespace

void addRawCopyChecks(ClangTidyCheckFactories &Factories) {
    Factories.registerCheck<AllowlistCheck>("cplusp-allowlist");
    Factories.registerCheck<RawCopyCheck>("cplusp-raw-copy");
}

} // namespace cplusp::detail
