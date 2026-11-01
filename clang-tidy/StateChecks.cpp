#include "CplusPChecks.h"

#include "clang/Basic/CodeGenOptions.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Lex/HeaderSearchOptions.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "clang/Serialization/ASTReader.h"
#include "clang/Serialization/ModuleManager.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar/SROA.h"

namespace cplusp::detail {

namespace {
// ------------------------------------------------------------ unlisted state, decisions 0035 and 0036

} // namespace

// The contract lines of the function that starts at `First`: the contiguous lines above that line that start with `//@`. A
// `CPLUSP_...(...)` marker line does not end the block. Any other line does. The lines come from the source buffer, because `//@`
// is no doc comment and the AST has not got it. A line that holds code before its `//@` is no contract line, so the walk stops at it.
// `Floor` is where the walk ends: it claims no line that starts at or above the line of `Floor`. A loop sets it to the start of the
// body of its function.
// ponytail: a floor in another file than the loop, as under a macro, is ignored. Such a loop can then claim its function's lines, and
// the core refuses them as lines in the wrong place, which is loud. Upgrade: compare the lines in the file of the loop's expansion.
// `SkipComments` steps over a whole-line `//` comment that is no `//@` line, and over a one-line `/* */` comment, decision 0099. Only the lines
// of a body use it.
// ponytail: a block comment over several lines ends the walk. Upgrade: the lexer's comment tokens.
Contract contractAbove(const SourceManager &SM, SourceLocation First, SourceLocation Floor, bool SkipComments) {
  Contract C;
  First = SM.getExpansionLoc(First);
  if (First.isInvalid())
    return C;
  const auto [File, Offset] = SM.getDecomposedLoc(First);
  bool Invalid = false;
  const StringRef Text = SM.getBufferData(File, &Invalid);
  if (Invalid)
    return C;
  size_t Start = Text.substr(0, Offset).rfind('\n');
  Start = Start == StringRef::npos ? 0 : Start + 1;
  size_t FloorStart = 0;
  if (Floor.isValid()) {
    const auto [FloorFile, FloorOffset] = SM.getDecomposedLoc(SM.getExpansionLoc(Floor));
    if (FloorFile == File) {
      const size_t Newline = Text.substr(0, FloorOffset).rfind('\n');
      FloorStart = Newline == StringRef::npos ? 0 : Newline + 1;
    }
  }
  while (Start > FloorStart) {
    // The line above is the text from the newline before it up to the newline that ends it.
    const size_t End = Start - 1;
    size_t Begin = Text.substr(0, End).rfind('\n');
    Begin = Begin == StringRef::npos ? 0 : Begin + 1;
    StringRef Line = Text.slice(Begin, End).trim();
    Start = Begin;
    if (Begin <= FloorStart && Floor.isValid())
      break;
    if (Line.starts_with("CPLUSP_"))
      continue;
    if (SkipComments && ((Line.starts_with("//") && !Line.starts_with("//@")) || (Line.starts_with("/*") && Line.ends_with("*/"))))
      continue;
    // A comment that ends in a backslash goes on in the next line. So the line above can be the tail of a `//@` line.
    size_t Head = Begin;
    while (Head > 0) {
      const size_t PreviousBegin = Text.substr(0, Head - 1).rfind('\n');
      const size_t From = PreviousBegin == StringRef::npos ? 0 : PreviousBegin + 1;
      if (!Text.slice(From, Head - 1).rtrim().ends_with("\\"))
        break;
      Head = From;
    }
    const bool Spliced = Head != Begin;
    if (Spliced) {
      Line = Text.slice(Head, Text.find('\n', Head)).trim();
      Begin = Start = Head;
    }
    if (!Line.consume_front("//@"))
      break;
    Line = Line.ltrim();
    C.Lines.push_back({SM.getLineNumber(File, static_cast<unsigned>(Begin)), Line.str(), {}, File});
    if (Spliced)
      continue;
    C.Any = true;
    std::vector<std::string> *Names = Line.consume_front("modifies") ? &C.Modifies : Line.consume_front("reads") ? &C.Reads : nullptr;
    if (!Names || (!Line.empty() && !isspace(static_cast<unsigned char>(Line.front()))))
      continue;
    llvm::SmallVector<StringRef, 8> Parts;
    Line.split(Parts, ',', -1, false);
    for (StringRef Name : Parts)
      if (!Name.trim().empty())
        Names->push_back(Name.trim().str());
  }
  std::reverse(C.Lines.begin(), C.Lines.end());  // the walk went upward
  return C;
}

namespace {

// Where a function starts: its return type, or its name for a constructor. A function template starts at its `template`, and its
// lines sit above that, as in examples/templates.
SourceLocation firstTokenOf(const FunctionDecl *Function) {
  // An abbreviated function template has no `template` keyword, and it begins at its return type, decision 0049.
  if (const FunctionTemplateDecl *Template = Function->getDescribedFunctionTemplate();
      Template && Template->getTemplateParameters()->getTemplateLoc().isValid())
    return Template->getBeginLoc();
  return Function->getOuterLocStart();
}

} // namespace

// ponytail: one ceiling. The lines come from the files of this translation unit, outside the system headers.
// A callee with no lines here brings no lines. So the contract of a callee in a header behind -isystem, or in another file, is not read.
// What its code does still counts, if the translation unit has the body.
// A callee with no body and no lines at all is refused.
// Upgrade: a contract reader that runs on every file, and a record of the lines of every function.
Contract contractOf(const SourceManager &SM, const FunctionDecl *Function) {
  Contract C;
  if (const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern())
    Function = Pattern;
  for (const FunctionDecl *Declaration : Function->redecls()) {
    // The compiler's own functions have no place in the source, and the place of an implicit member is its class.
    if (Declaration->isImplicit() || SM.isInSystemHeader(Declaration->getLocation()))
      continue;
    Contract One = contractAbove(SM, firstTokenOf(Declaration));
    for (Contract::Line &L : One.Lines)
      for (const ParmVarDecl *P : Declaration->parameters())
        L.Params.push_back(P->getNameAsString());
    for (const ParmVarDecl *P : Declaration->parameters())
      if (P->getType()->isLValueReferenceType() && !P->getType()->getPointeeType().isConstQualified())
        C.Parameters.push_back(P->getNameAsString());
    C.Modifies.insert(C.Modifies.end(), One.Modifies.begin(), One.Modifies.end());
    C.Reads.insert(C.Reads.end(), One.Reads.begin(), One.Reads.end());
    C.Any |= One.Any;
    C.Lines.insert(C.Lines.end(), One.Lines.begin(), One.Lines.end());
  }
  return C;
}

namespace {

// The name of a variable as a contract line writes it: qualified, and without the arguments of a class template, so `Box<int>::n` is
// `Box::n`.
std::string nameOf(const VarDecl *Var) {
  std::string Name;
  int Depth = 0;
  for (const char C : Var->getQualifiedNameAsString()) {
    if (C == '<')
      ++Depth;
    else if (C == '>' && Depth > 0)
      --Depth;
    else if (Depth == 0)
      Name += C;
  }
  return Name;
}

// A mutable global or a static data member. A constant, a member and a function-local static are not state here.
bool isState(const VarDecl *Var) { return isMutableGlobal(Var) && !Var->isStaticLocal(); }

// The methods whose lines hold the overrides of `Base`: `Base` itself, or, when nobody wrote `Base`, what it overrides, as far up as that
// goes. The destructor that the compiler wrote for a class has no lines, and its overrides answer to the lines above it. A function
// that is declared `= default` is written, and its lines are its own, empty or not.
std::vector<const CXXMethodDecl *> lineHolders(const CXXMethodDecl *Base) {
  std::vector<const CXXMethodDecl *> Out;
  if (Base->isImplicit())
    for (const CXXMethodDecl *Up : Base->overridden_methods()) {
      const auto More = lineHolders(Up);
      Out.insert(Out.end(), More.begin(), More.end());
    }
  if (Out.empty())
    Out.push_back(Base);
  return Out;
}

// The state variable that a listed name names. A name is the qualified name of the variable, or that name after a `::`, and it names
// the variable only when no other state variable of the whole translation unit matches it too: two statics called `n` are named by
// none, and so are two that end in `C::k`.
const std::string *resolve(StringRef Listed, const std::vector<std::string> &State) {
  const std::string *Found = nullptr;
  for (const std::string &Name : State) {
    const StringRef Full = Name;
    if (Full == Listed || (Full.size() > Listed.size() && Full.ends_with(Listed) && Full.drop_back(Listed.size()).ends_with("::"))) {
      if (Found)
        return nullptr;
      Found = &Name;
    }
  }
  return Found;
}

// A function with a body in this translation unit, or whose pattern has one.
bool hasBody(const FunctionDecl *Function) {
  const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern();
  return Function->isDefined() || (Pattern && Pattern->isDefined());
}

// The state variables that a list of lines names. A name that no variable has is a parameter or a typo, and the prover has it. A name of a
// parameter of the function is the parameter, even when a variable has the same name, decision 0111.
std::set<std::string> namedState(const std::vector<std::string> &Lines, const std::vector<std::string> &State, const std::vector<std::string> &Parameters = {}) {
  std::set<std::string> Names;
  for (const std::string &Line : Lines)
    if (const std::string *Var = std::find(Parameters.begin(), Parameters.end(), Line) == Parameters.end() ? resolve(Line, State) : nullptr)
      Names.insert(*Var);
  return Names;
}

// The declaration is in the C++ ABI of the compiler's runtime, which the library calls to throw and to catch.
// ponytail: a name test. Another runtime library's namespace is not known. Upgrade: a list of the runtime's namespaces.
bool inAbiNamespace(const Decl *Declaration) {
  for (const DeclContext *Context = Declaration->getDeclContext(); Context; Context = Context->getParent())
    if (const auto *Namespace = dyn_cast<NamespaceDecl>(Context); Namespace && Namespace->getName() == "__cxxabiv1")
      return true;
  return false;
}

// The state a file declares, outside the system headers: in a namespace, a linkage specification, a class or a class template.
void collectState(const DeclContext *Context, const SourceManager &SM, std::vector<std::string> &Out) {
  for (const Decl *D : Context->decls()) {
    if (SM.isInSystemHeader(D->getLocation()))
      continue;
    if (const auto *Var = dyn_cast<VarDecl>(D)) {
      if (isState(Var))
        Out.push_back(nameOf(Var));
    } else if (const auto *Template = dyn_cast<ClassTemplateDecl>(D)) {
      collectState(Template->getTemplatedDecl(), SM, Out);
    } else if (const auto *Template = dyn_cast<VarTemplateDecl>(D)) {
      if (isState(Template->getTemplatedDecl()))
        Out.push_back(nameOf(Template->getTemplatedDecl()));
    } else if (isa<NamespaceDecl, LinkageSpecDecl, CXXRecordDecl>(D)) {
      collectState(cast<DeclContext>(D), SM, Out);
    }
  }
}

// ------------------------------------------------------------ the markers of a function, decisions 0039 and 0047

// The kind a `cplusp:` annotation names, and none when the word is no marker. `cplusp:assume` marks one statement and waits for a case
// that needs it, so on a declaration it is no marker.
enum class MarkerKind { None, Verified, Trusted, Plain };

MarkerKind markerKind(StringRef Annotation) {
  if (Annotation == "cplusp:verified")
    return MarkerKind::Verified;
  if (Annotation == "cplusp:trusted")
    return MarkerKind::Trusted;
  if (Annotation == "cplusp:plain")
    return MarkerKind::Plain;
  return MarkerKind::None;
}

// The declarations of a function in the order the compiler met them. The declarations of a function template are linked the same way.
std::vector<const FunctionDecl *> declarationsOf(const FunctionDecl *Function) {
  std::vector<const FunctionDecl *> Out;
  for (const FunctionDecl *D = Function->getMostRecentDecl(); D; D = D->getPreviousDecl())
    Out.push_back(D);
  std::reverse(Out.begin(), Out.end());
  return Out;
}

// The compiler makes the first declaration of an explicit specialization from its template, with a copy of the attributes. The copy has
// the place of the attribute that it was copied from, so a specialization has a marker only when it wrote one in a place of its own.
bool copiedFromTemplate(const FunctionDecl *Declaration, const Attr *A) {
  if (const FunctionDecl *Pattern = Declaration->getTemplateInstantiationPattern(false))
    for (const FunctionDecl *Of : declarationsOf(Pattern))
      for (const Attr *Original : Of->attrs())
        if (Original->getLocation() == A->getLocation())
          return true;
  return false;
}

// The `cplusp:` annotations that a declaration wrote itself. A later declaration inherits a copy of each, and the copy is skipped.
template <typename F> void forEachMarker(const Decl *Declaration, const F &Visit) {
  const auto *Function = dyn_cast<FunctionDecl>(Declaration);
  for (const Attr *A : Declaration->attrs())
    if (const auto *Note = dyn_cast<AnnotateAttr>(A);
        Note && !A->isInherited() && Note->getAnnotation().starts_with("cplusp:") && !(Function && copiedFromTemplate(Function, A)))
      Visit(Note);
}

// The function an instantiation was made from. Any other function is its own, an explicit specialization too.
const FunctionDecl *patternOf(const FunctionDecl *Function) {
  const FunctionDecl *Pattern = Function->getTemplateInstantiationPattern();
  return Pattern ? Pattern : Function;
}

// The kind of the markers written on the declarations of a function itself, decision 0047. None when no declaration has a marker, and
// none when two name two kinds.
MarkerKind declaredKind(const FunctionDecl *Function) {
  MarkerKind Kind = MarkerKind::None;
  bool Twice = false;
  for (const FunctionDecl *D : declarationsOf(patternOf(Function)))
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      const MarkerKind Named = markerKind(Note->getAnnotation());
      if (Named == MarkerKind::None)
        return;
      if (Kind == MarkerKind::None)
        Kind = Named;
      else if (Kind != Named)
        Twice = true;
    });
  return Twice ? MarkerKind::None : Kind;
}

// Whether a class carries a plain marker on a declaration of its own, decision 0051. An instantiation of a class template has a copy of
// the marker of its pattern. An explicit or a partial specialization is a class of its own and needs a marker of its own, as decision
// 0047 says of the specialization of a function.
bool markedPlain(const CXXRecordDecl *Record) {
  for (const TagDecl *D : Record->redecls())
    for (const Attr *A : D->attrs())
      if (const auto *Note = dyn_cast<AnnotateAttr>(A); Note && markerKind(Note->getAnnotation()) == MarkerKind::Plain)
        return true;
  return false;
}

// The declaration around `D` that holds its name, or the one that holds its text.
const Decl *outerOf(const Decl *D, bool Written) {
  const DeclContext *Outer = Written ? D->getLexicalDeclContext() : D->getDeclContext();
  return Outer ? Decl::castFromDeclContext(Outer) : nullptr;
}

// A friend function whose definition is this declaration.
bool definedFriend(const Decl *D) {
  const auto *F = dyn_cast<FunctionDecl>(D);
  return F && F->getFriendObjectKind() != Decl::FOK_None && F->isThisDeclarationADefinition();
}

} // namespace

// Whether `D` is plain, `D` itself included. Code in a plain function is plain, decision 0048: a lambda, a local class and its members,
// however deep. Clang takes no marker on a lambda, and a plain body is out of the gate's view. A plain class is the same, decision 0051:
// its members, its nested types and the lambdas in it are plain. So is a member defined outside it and a member that the compiler writes.
// The walk goes by where the name lives. A member with a marker of its own, trusted or verified, has that kind, so the class does not
// hold it or the code inside it, as decision 0047 says. A lambda or a local class in a trusted body stays verified.
// A friend is no member, but one that the class defines is code in the body of the class, decision 0053. Its name lives outside the
// class, so the walk goes by where it is written, which keeps the regions and the rule on calls of one mind. A friend that the class only
// declares keeps the kind of its definition.
bool insidePlain(const Decl *D) {
  bool Marked = false;
  for (; D; D = outerOf(D, definedFriend(D)))
    if (const auto *Enclosing = dyn_cast<FunctionDecl>(D)) {
      const MarkerKind Own = declaredKind(Enclosing);
      if (Own == MarkerKind::Plain)
        return true;
      Marked |= Own != MarkerKind::None;
    } else if (const auto *Class = dyn_cast<CXXRecordDecl>(D); Class && !Marked && markedPlain(Class)) {
      return true;
    }
  return false;
}

namespace {

// Whether the text of `D` is inside the region of something plain that holds it, so that `D` needs no region of its own. A member
// defined outside its class is plain and it is written outside the class.
bool coveredByPlain(const Decl *D) { return insidePlain(D) && insidePlain(outerOf(D, true)); }

// ------------------------------------------------------------ the lowered form, decision 0037

// What a piece of code does to the state: the names it writes and reads, and its refusals. A refusal is a whole message, so the
// function that is judged can report it at the instruction that brought it.
struct Effect {
  std::set<std::string> Writes, Reads, Refusals;
  size_t size() const { return Writes.size() + Reads.size() + Refusals.size(); }
  // Whether this grew.
  bool add(const Effect &Other) {
    const size_t Before = size();
    Writes.insert(Other.Writes.begin(), Other.Writes.end());
    Reads.insert(Other.Reads.begin(), Other.Reads.end());
    Refusals.insert(Other.Refusals.begin(), Other.Refusals.end());
    return size() != Before;
  }
};

// A place in a file, as the debug line table gives it: the file, a line and a column.
// The file is the entry of the file manager. So a header that is included twice is one file, and its lines are the same in both.
struct Place {
  const FileEntry *File = nullptr;
  unsigned Line = 0, Col = 0;
  bool before(const Place &O) const { return Line != O.Line ? Line < O.Line : Col < O.Col; }
};

// A virtual call of the tree: where it is written, the method that the source names, and the function that holds the expression.
// The owner is the canonical declaration of that instantiation, or none if no function holds it.
// The lowered form has an indirect call there. Two functions of a library may hold a call on the same line of a header.
// So the owner tells them apart. The place is numbers, and no source location.
// The second inclusion of a header is another file in the source manager, and the same file in the line table.
struct VirtualCall {
  Place Begin, End;
  const CXXMethodDecl *Method;
  const FunctionDecl *Owner;
};

struct Finding {
  SourceLocation Loc;
  std::string Message;
};

// The code that clang generates for a translation unit, and what each function in it does to the state. Both the state check and the
// sequencing check ask it. It is built once, at the end of the translation unit, on the first question.
class Lowered {
public:
  // What the matchers give it. The virtual calls of the tree. The functions that the file wrote, which the module must hold whether
  // anything calls them or not. Every instantiation of a template, which clang hands to its code generator as it makes it.
  ASTContext *Ctx = nullptr;
  std::vector<VirtualCall> Virtuals;
  std::vector<const FunctionDecl *> Judged, Instances;
  std::vector<const VarDecl *> VarInstances;

  void addVirtual(SourceRange Where, const CXXMethodDecl *Method, const FunctionDecl *Owner) {
    Virtuals.push_back({placeOfExpansion(Where.getBegin()), placeOfExpansion(Where.getEnd()), Method, Owner ? Owner->getCanonicalDecl() : nullptr});
  }

  // Where a location of the tree is, as the line table would give it.
  Place placeOfExpansion(SourceLocation Loc) const {
    const SourceManager &SM = Ctx->getSourceManager();
    const auto [File, Offset] = SM.getDecomposedExpansionLoc(Loc);
    return {SM.getFileEntryForID(File), SM.getLineNumber(File, Offset), SM.getColumnNumber(File, Offset)};
  }

  // The first check to match gives the context.
  void use(ASTContext *Context) {
    if (!Ctx)
      Ctx = Context;
  }

  // The qualified names of the state of this file, found once per translation unit.
  const std::vector<std::string> &state() {
    if (!Collected) {
      collectState(Ctx->getTranslationUnitDecl(), Ctx->getSourceManager(), State);
      llvm::sort(State);
      State.erase(std::unique(State.begin(), State.end()), State.end());
      Collected = true;
    }
    return State;
  }

  // The findings of the state check: one per message per line, found by judging every function that the file wrote.
  const std::vector<Finding> &findings() {
    build();
    return Findings;
  }

  // A call that runs a plain function, decision 0047: where the call is, and the qualified name of the plain function.
  struct PlainCall {
    SourceLocation Loc;
    std::string Name;
  };
  // The calls of the code that the file wrote, from every function of it whatever its kind, that run a plain function. A call runs it
  // when it names it, when the library or a member that the compiler wrote reaches it, when a virtual call can reach it, or when it
  // passes it on as a function constant. The gate asks the kind of the place.
  const std::vector<PlainCall> &plainCalls() {
    build();
    return PlainCalls;
  }

  // The calls of the code that the file wrote that can run an indirect call with no target that the gate can name, decision 0048.
  const std::vector<SourceLocation> &indirectCalls() {
    build();
    return IndirectCalls;
  }

  // False when the compiler could not generate code for the file. Then no call is read.
  bool generated() {
    build();
    return !Failed;
  }

  // Whether a call of `Callee` changes state, as far as its lines and the lowered form say. The first part of the sequencing check's
  // rule, a mutable parameter or a non-const method, is the caller's.
  bool changes(const FunctionDecl *Callee) {
    build();
    if (!contractOf(Ctx->getSourceManager(), Callee).Modifies.empty())
      return true;
    // A file that clang cannot generate code for is refused by the state check. A call that the table cannot read is a change, as a
    // refusal is.
    if (Failed)
      return true;
    const auto Found = ByDecl.find(Callee->getCanonicalDecl());
    if (Found == ByDecl.end()) {
      if (!hasBody(Callee) && opaque(Callee))
        return true;
    } else if (Fns.find(Found->second)->second.Is == Role::Edge ? !edge(Callee).Refusals.empty() : Fns.find(Found->second)->second.Deep) {
      return true;
    }
    // A call through a base may run any override of it in the module.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(Callee))
      for (const llvm::Function *F : Overriders.lookup(cast<CXXMethodDecl>(Method->getCanonicalDecl())))
        if (Fns.find(F)->second.Deep || !contractOf(Ctx->getSourceManager(), Fns.find(F)->second.FD).Modifies.empty())
          return true;
    return false;
  }

private:
  enum class Role { Judged, Carrier, Edge };
  // What a function calls, in the module. The carriers are for the fixpoint of the effects.
  // Every function that has a body is for the bit that the sequencing check reads.
  struct Calls {
    std::vector<const llvm::Function *> Carriers, Bodies;
  };
  // A function of the module, with the declaration of the tree that it came from.
  // A carrier has no lines of its own, so it brings its effect `E` to whoever calls it.
  // A function that the file wrote has its effect too. A call of it brings its lines, and the state check reads one level of tags.
  // That is decision 0037. The sequencing check asks `Deep`. It is set when the code of the function stores a global of the state or
  // holds a refusal. It is also set when the code of anything with a body that it calls does, at any depth. No line stops it.
  // It is also set when the lines of a callee list a name on `modifies`, because `bring` puts those names in `Writes`.
  struct Fn {
    const FunctionDecl *FD = nullptr;
    Role Is = Role::Carrier;
    Effect E;
    Calls C;
    bool Deep = false;
  };
  // Where a pointer comes from. A refusal holds its message, or none for a pointer the gate cannot follow.
  struct Root {
    enum Kind { Global, Local, Func, Refuse } K;
    const llvm::Value *V;
    std::string Why;
  };
  // The objects that a walk has been to, and whether it came through a load of a pointer.
  using Seen = llvm::SmallSet<std::pair<const llvm::Value *, bool>, 16>;

  // The generated module has to outlive nothing of the tree, so the maps below hold what the tree knows about it.
  llvm::LLVMContext LLVM;
  CodeGenOptions CGO;
  HeaderSearchOptions HSO;
  PreprocessorOptions PPO;
  std::unique_ptr<DiagnosticsEngine> Diags;
  std::unique_ptr<CodeGenerator> Gen;
  std::unique_ptr<llvm::Module> Mod;
  llvm::DenseMap<const llvm::Function *, Fn> Fns;
  llvm::DenseMap<const FunctionDecl *, const llvm::Function *> ByDecl;
  llvm::DenseMap<const llvm::GlobalVariable *, std::string> StateOf;
  llvm::DenseMap<const llvm::GlobalVariable *, const VarDecl *> VarOf;
  llvm::DenseSet<const llvm::GlobalVariable *> Known, Library;
  // The loads that find the function of a virtual call, which the match of the call judges.
  llvm::DenseSet<const llvm::Instruction *> Dispatch;
  llvm::DenseMap<const llvm::CallBase *, std::vector<const VirtualCall *>> Matched;
  llvm::DenseMap<const CXXMethodDecl *, std::vector<const llvm::Function *>> Overriders;
  llvm::DenseMap<const llvm::DIFile *, const FileEntry *> Files;
  std::set<std::pair<std::pair<unsigned, unsigned>, std::string>> Reported;
  std::vector<std::string> State;
  std::vector<Finding> Findings;
  std::vector<PlainCall> PlainCalls;
  std::set<std::pair<SourceLocation::UIntTy, std::string>> PlainSeen;
  std::vector<SourceLocation> IndirectCalls;
  std::set<SourceLocation::UIntTy> IndirectSeen;
  bool Collected = false, Built = false, Failed = false;

  // ------------------------------------------------------------ build

  void build() {
    if (Built)
      return;
    Built = true;
    SourceManager &SM = Ctx->getSourceManager();
    const bool Generated = generate();
    // The generator holds the tree, which is gone by the next translation unit.
    Gen.reset();
    if (!Generated) {
      Failed = true;
      Findings.push_back({SM.getLocForStartOfFile(SM.getMainFileID()),
                          "global_state: the compiler could not generate code for this file, so the state check cannot run."});
      return;
    }
    markDispatch();
    // The effect of each function with a body, from its own instructions, then grown by what its carriers bring until nothing changes.
    // Effects only grow and the names are finite, so it ends.
    for (auto &[F, Info] : Fns)
      if (Info.Is != Role::Edge)
        for (const llvm::BasicBlock &BB : *F)
          for (const llvm::Instruction &I : BB)
            instruction(I, Info.E, &Info.C);
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, Info] : Fns)
        for (const llvm::Function *Dep : Info.C.Carriers)
          if (Dep != F)
            Changed |= Info.E.add(Fns.find(Dep)->second.E);
    }
    // The bit for the sequencing check, by the same kind of fixpoint over every call that has a body.
    for (auto &[F, Info] : Fns)
      Info.Deep = !Info.E.Writes.empty() || !Info.E.Refusals.empty();
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, Info] : Fns)
        if (!Info.Deep)
          for (const llvm::Function *Dep : Info.C.Bodies)
            if (Fns.find(Dep)->second.Deep) {
              Info.Deep = Changed = true;
              break;
            }
    }
    for (const auto &[F, Info] : Fns)
      if (Info.Is == Role::Judged)
        judge(*F, Info.FD);
    holdOverrides();
    plainCode();
    indirectCode();
  }

  // Generate the module for the translation unit that the matchers have just read, and read the tree's names off it. False if clang
  // cannot generate code for it.
  bool generate() {
    SourceManager &SM = Ctx->getSourceManager();
    // The tree of a file that does not compile is no input for code generation.
    if (Ctx->getDiagnostics().hasErrorOccurred())
      return false;
    // The diagnostics of code generation are the gate's business, and the gate says one thing about them. A fresh engine counts them.
    Diags = std::make_unique<DiagnosticsEngine>(new DiagnosticIDs, new DiagnosticOptions, new IgnoringDiagConsumer);
    Diags->setSourceManager(&SM);
    // Clang marks a load of a pointer to a vtable `!invariant.group` only when it optimizes, and only when it is told to. It does the
    // marking while it generates code. The module gets no pass but SROA below, so nothing is inlined.
    CGO.OptimizationLevel = 1;
    CGO.StrictVTablePointers = true;
    CGO.setDebugInfo(llvm::codegenoptions::DebugLineTablesOnly);
    CGO.DebugColumnInfo = true;
    Gen.reset(CreateLLVMCodeGen(*Diags, "cplusp", SM.getFileManager().getVirtualFileSystemPtr(), HSO, PPO, CGO, LLVM));
    Gen->Initialize(*Ctx);
    // A copy, because code generation may add declarations to the translation unit.
    const std::vector<Decl *> Top(Ctx->getTranslationUnitDecl()->decls_begin(), Ctx->getTranslationUnitDecl()->decls_end());
    for (Decl *D : Top)
      Gen->HandleTopLevelDecl(DeclGroupRef(D));
    for (const FunctionDecl *FD : Instances)
      Gen->HandleTopLevelDecl(DeclGroupRef(const_cast<FunctionDecl *>(FD)));
    // A table of function pointers is an instantiated variable, and the call through it needs its initializer.
    // Sema hands every instantiated variable definition to the generator this way, a static data member or a variable template.
    for (const VarDecl *Var : VarInstances)
      Gen->HandleCXXStaticMemberVarInstantiation(const_cast<VarDecl *>(Var));
    // An inline function that nothing calls is no part of a build, and the gate judges it all the same. So is a static one.
    for (const FunctionDecl *FD : Judged) {
      const auto *Method = dyn_cast<CXXMethodDecl>(FD);
      if (FD->isDeleted() || FD->isImmediateFunction() || (Method && isLambdaCallOperator(Method)))
        continue;
      if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(FD))
        Gen->GetAddrOfGlobal(GlobalDecl(Constructor, Ctor_Complete), true);
      else if (const auto *Destructor = dyn_cast<CXXDestructorDecl>(FD))
        Gen->GetAddrOfGlobal(GlobalDecl(Destructor, Dtor_Complete), true);
      else
        Gen->GetAddrOfGlobal(GlobalDecl(FD), true);
    }
    Gen->HandleTranslationUnit(*Ctx);
    llvm::Module *M = Gen->GetModule();
    if (!M || Diags->hasErrorOccurred())
      return false;
    // SROA, so that a reference held in a local resolves to what it names.
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    llvm::ModulePassManager MPM;
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    for (llvm::Function &F : *M)
      if (!F.isDeclaration())
        F.removeFnAttr(llvm::Attribute::OptimizeNone);
    MPM.run(*M, MAM);
    for (llvm::Function &F : *M) {
      Fn &Info = Fns[&F];
      Info.FD = dyn_cast_or_null<FunctionDecl>(Gen->GetDeclForMangledName(F.getName()));
      Info.Is = F.isDeclaration() ? Role::Edge : Info.FD && isJudged(Info.FD, SM) ? Role::Judged : Role::Carrier;
      if (Info.FD)
        ByDecl.try_emplace(Info.FD->getCanonicalDecl(), &F);
    }
    // A global that the tree does not know, such as a vtable, a string or a guard variable, is no state.
    for (llvm::GlobalVariable &G : M->globals())
      if (const auto *Var = dyn_cast_or_null<VarDecl>(Gen->GetDeclForMangledName(G.getName()))) {
        // A global of a system header is the library's own, as the pointer to a callable that std::call_once keeps in one.
        (SM.isInSystemHeader(Var->getLocation()) ? Library : Known).insert(&G);
        VarOf[&G] = Var;
        if (isState(Var))
          StateOf[&G] = nameOf(Var);
      }
    for (const auto &[F, Info] : Fns)
      if (const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD))
        overrides(Method, F);
    Mod.reset(Gen->ReleaseModule());
    return true;
  }

  // `F` is the code of `Method`, and so of everything that `Method` overrides, however far up.
  void overrides(const CXXMethodDecl *Method, const llvm::Function *F) {
    for (const CXXMethodDecl *Base : Method->overridden_methods()) {
      auto &List = Overriders[cast<CXXMethodDecl>(Base->getCanonicalDecl())];
      if (!llvm::is_contained(List, F)) {
        List.push_back(F);
        overrides(Base, F);
      }
    }
  }

  // The virtual calls of the tree that an indirect call of the module is. Only the calls that the function holds count.
  // A call that no function holds counts wherever it is. One in a default member initializer is such a call.
  // Every function that makes the object runs it.
  const std::vector<const VirtualCall *> &matched(const llvm::CallBase &CB) {
    const auto Cached = Matched.find(&CB);
    if (Cached != Matched.end())
      return Cached->second;
    auto &Out = Matched[&CB];
    const Place At = placeOf(CB);
    const FunctionDecl *Holder = Fns.find(CB.getFunction())->second.FD;
    if (Holder)
      Holder = Holder->getCanonicalDecl();
    if (At.File)
      for (const VirtualCall &V : Virtuals)
        if (V.Begin.File == At.File && (!V.Owner || V.Owner == Holder) && !At.before(V.Begin) && !V.End.before(At))
          Out.push_back(&V);
    return Out;
  }

  // The virtual dispatches that an indirect call may be. The callee is a slot read from a table.
  // The pointer to the table is a load that clang marked `!invariant.group`.
  // The callee may be a choice between a slot and something else, as a pointer to a member function is.
  // Each dispatch is the load of the slot and the load of the table.
  static llvm::SmallVector<std::pair<const llvm::LoadInst *, const llvm::LoadInst *>, 2> dispatchesOf(const llvm::CallBase &CB) {
    llvm::SmallVector<std::pair<const llvm::LoadInst *, const llvm::LoadInst *>, 2> Out;
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(CB.getCalledOperand(), Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      const auto *Slot = dyn_cast<llvm::LoadInst>(O);
      if (!Slot)
        continue;
      const llvm::Value *P = Slot->getPointerOperand();
      while (const auto *G = dyn_cast<llvm::GEPOperator>(P))
        P = G->getPointerOperand();
      const auto *Table = dyn_cast<llvm::LoadInst>(P);
      if (Table && Table->hasMetadata(llvm::LLVMContext::MD_invariant_group))
        Out.push_back({Slot, Table});
    }
    return Out;
  }

  // The function that a virtual call finds is read from the object: the pointer to the table, then the slot in it.
  // When the tree has the call, the match judges them. So the pointer to the table of a global object needs no following.
  void markDispatch() {
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge)
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          const auto *CB = dyn_cast<llvm::CallBase>(&I);
          if (!CB || CB->isInlineAsm() || calleeOf(*CB) || matched(*CB).empty())
            continue;
          for (const auto &[Slot, Table] : dispatchesOf(*CB)) {
            Dispatch.insert(Slot);
            Dispatch.insert(Table);
          }
        }
    }
  }

  // One finding for a line and a message.
  void report(SourceLocation Loc, const std::string &Message) {
    const SourceManager &SM = Ctx->getSourceManager();
    if (Reported.insert({{SM.getFileID(Loc).getHashValue(), SM.getExpansionLineNumber(Loc)}, Message}).second)
      Findings.push_back({SM.getExpansionLoc(Loc), Message});
  }

  // An override lists no more than the function it overrides. So a call through the base brings lines that hold for every override.
  // The check of the tree holds a method that has lines. This holds the one that nobody wrote, by what it runs.
  // The destructor of a class with a member that has a destructor of its own is such a method.
  void holdOverrides() {
    const SourceManager &SM = Ctx->getSourceManager();
    for (const auto &[F, Info] : Fns) {
      const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD);
      if (Info.Is != Role::Carrier || !Method)
        continue;
      const SourceLocation At = Method->getParent()->getLocation();
      for (const CXXMethodDecl *Direct : Method->overridden_methods())
        for (const CXXMethodDecl *Base : lineHolders(Direct)) {
          if (SM.isInSystemHeader(Base->getLocation()))
            continue;
          const Effect Up = linesOf(Base);
          const std::string Of = Method->getNameAsString(), Over = Base->getQualifiedNameAsString();
          for (const std::string &Name : Info.E.Writes)
            if (!Up.Writes.count(Name))
              report(At, "global_state: " + Of + " changes " + Name + ", and the modifies line of " + Over + " does not list it.");
          for (const std::string &Name : Info.E.Reads)
            if (!Up.Writes.count(Name) && !Up.Reads.count(Name))
              report(At, "global_state: " + Of + " reads " + Name + ", and no reads or modifies line of " + Over + " lists it.");
        }
    }
  }

  // A user-written function with a definition in a user file. A lambda's call operator has no lines of its own, so it is a carrier.
  static bool isJudged(const FunctionDecl *FD, const SourceManager &SM) {
    const auto *Method = dyn_cast<CXXMethodDecl>(FD);
    return FD->isThisDeclarationADefinition() && !SM.isInSystemHeader(SM.getExpansionLoc(FD->getBeginLoc())) && !notJudgedFunction(*FD) &&
           !(Method && isLambdaCallOperator(Method));
  }

  // ------------------------------------------------------------ lines and edges

  // What the lines of a function name: the state it lists as changed and as read.
  Effect linesOf(const FunctionDecl *FD) {
    const Contract C = contractOf(Ctx->getSourceManager(), FD);
    Effect E;
    E.Writes = namedState(C.Modifies, state(), C.Parameters);
    E.Reads = namedState(C.Reads, state(), C.Parameters);
    return E;
  }

  // A function that the gate cannot read: no body in the lowered form, and no contract lines. A call of it may change any global. A
  // function that the compiler or a `= default` defines, and a pure virtual function, which an override answers, are no such function.
  bool opaque(const FunctionDecl *FD) {
    return !(FD->isImplicit() || FD->isDefaulted() || FD->isPureVirtual()) && !contractOf(Ctx->getSourceManager(), FD).Any;
  }

  // A function with no body in the module. A system header declares it, or it is a builtin: it brings nothing. Otherwise it brings its
  // lines, and without any the call is refused, whatever namespace the function is in.
  Effect edge(const FunctionDecl *FD) {
    Effect E;
    const SourceManager &SM = Ctx->getSourceManager();
    if (!FD || FD->getBuiltinID() || SM.isInSystemHeader(FD->getLocation()))
      return E;
    E.add(linesOf(FD));
    if (opaque(FD))
      E.Refusals.insert("global_state: " + FD->getNameAsString() + " has no body here and no contract lines, so it may change any global.");
    return E;
  }

  // What a call of `F` brings: the lines of a function the file wrote, the effect of a carrier, what an edge says. A carrier's effect is
  // still growing while the carriers are read, so then the callee is recorded for the fixpoint.
  void bring(const llvm::Function *F, Effect &E, Calls *D) {
    const Fn &Info = Fns.find(F)->second;
    switch (Info.Is) {
    case Role::Judged:
      E.add(linesOf(Info.FD));
      if (D)
        D->Bodies.push_back(F);
      break;
    case Role::Carrier:
      if (D) {
        D->Carriers.push_back(F);
        D->Bodies.push_back(F);
      } else {
        E.add(Info.E);
      }
      break;
    case Role::Edge:
      E.add(edge(Info.FD));
      break;
    }
  }

  // ------------------------------------------------------------ instructions

  static const llvm::Function *calleeOf(const llvm::CallBase &CB) {
    return dyn_cast<llvm::Function>(CB.getCalledOperand()->stripPointerCastsAndAliases());
  }

  // The functions that a constant names, as a table of function pointers does.
  // An intrinsic is no function of the author's, as `llvm.launder.invariant.group` is not.
  // A global is not followed, except a private one with an initializer. The compiler made it for an initializer of its own.
  // A vtable is never private, so the store of its address in a constructor brings nothing.
  static void functionsIn(const llvm::Constant *C, std::vector<const llvm::Function *> &Out, llvm::SmallPtrSetImpl<const llvm::Constant *> &Done) {
    if (const auto *F = dyn_cast<llvm::Function>(C)) {
      if (!F->isIntrinsic())
        Out.push_back(F);
    } else if (const auto *G = dyn_cast<llvm::GlobalVariable>(C); G && G->hasPrivateLinkage() && G->hasInitializer()) {
      if (Done.insert(G).second)
        functionsIn(G->getInitializer(), Out, Done);
    } else if (!isa<llvm::GlobalValue, llvm::BlockAddress>(C) && Done.insert(C).second) {
      for (const llvm::Use &U : C->operands())
        if (const auto *Part = dyn_cast<llvm::Constant>(U.get()))
          functionsIn(Part, Out, Done);
    }
  }

  // A function whose address is an operand of an instruction, other than the callee of a direct call, may be called later.
  // The pointer that holds it may be called by code that has no way to know what the function does.
  // So the instruction brings what a call of it would bring. That covers a store of the address, a select, a phi, an argument and a
  // part of a constant. A constant that the compiler made for an initializer is followed, as the table of an array of function pointers is.
  // `call()` follows the table of the library, where the callee of an indirect call is read from such a global.
  void named(const llvm::Constant *C, Effect &E, Calls *D, llvm::SmallPtrSetImpl<const llvm::Constant *> &Done) {
    std::vector<const llvm::Function *> Functions;
    functionsIn(C, Functions, Done);
    for (const llvm::Function *F : Functions)
      bring(F, E, D);
  }

  // The address of a global that is put into an object lets whoever holds the object write the global, decisions 0225 and 0226. The gate does not follow
  // the object, so the store counts as a change of the global. This holds for a constant address, for a pointer that is no constant, such as a select of two
  // addresses, and for a constant array of the compiler that holds an address, such as the elements of a braced list.
  // ponytail: a store into a global is left out, and so is a pointer that a call gives back into a call that the gate can follow. A write through the
  // pointer is not told apart from a read, so any such store counts as a change. Upgrade: follow the object that holds the pointer.
  void stored(const llvm::Value *Into, const llvm::Value *V, Effect &E) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(Into, Objects, nullptr, 0);
    // The address of a thread_local global is the result of an intrinsic call.
    if (llvm::any_of(Objects, [](const llvm::Value *O) {
          const auto *Call = dyn_cast<llvm::IntrinsicInst>(O);
          return isa<llvm::GlobalVariable>(O) || (Call && Call->getIntrinsicID() == llvm::Intrinsic::threadlocal_address);
        }))
      return;
    // A pointer that is no constant is followed to its roots: a global counts as a change, and a pointer that the gate cannot follow is refused.
    if (const auto *C = dyn_cast<llvm::Constant>(V))
      addresses(C, true, E);
    else if (V->getType()->isPointerTy())
      access(V, true, E);
  }

  // The state globals whose address a constant holds. `CountTop` says whether the constant being a global of the state counts: a global that is the argument
  // of a call is judged by the parameter that it binds to, and a global inside a constant array or a struct is not. A pointer into a struct or an array that is
  // a global, such as `&g_s.y`, is that global, decision 0227. A constant global with a start value, of the compiler or of the file, is read for the addresses
  // in its start value, decision 0228.
  // ponytail: any address in the start value of a constant global that is the argument of a call counts as a change, whatever the call does with it. A read
  // through the constant would count too. Upgrade: judge the call by the parameter that binds the constant, as for a state global.
  void addresses(const llvm::Constant *Start, bool CountTop, Effect &E) {
    llvm::SmallPtrSet<const llvm::Constant *, 8> Done;
    llvm::SmallVector<std::pair<const llvm::Constant *, bool>, 8> Work{{Start, CountTop}};
    while (!Work.empty()) {
      auto [C, Counts] = Work.pop_back_val();
      if (C->getType()->isPointerTy())
        C = cast<llvm::Constant>(C->stripInBoundsConstantOffsets());
      if (!Done.insert(C).second)
        continue;
      if (const auto *G = dyn_cast<llvm::GlobalVariable>(C)) {
        if (const auto Name = StateOf.find(G); Name != StateOf.end()) {
          if (Counts)
            E.Writes.insert(Name->second);
        } else if (G->isConstant() && G->hasInitializer()) {
          Work.push_back({G->getInitializer(), true});
        }
        continue;
      }
      for (const llvm::Use &U : C->operands())
        if (const auto *Inner = dyn_cast<llvm::Constant>(U.get()))
          Work.push_back({Inner, true});
    }
  }

  void instruction(const llvm::Instruction &I, Effect &E, Calls *D) {
    llvm::SmallPtrSet<const llvm::Constant *, 8> Done;
    for (const llvm::Use &U : I.operands()) {
      const auto *CB = dyn_cast<llvm::CallBase>(&I);
      if (const auto *C = dyn_cast<llvm::Constant>(U.get()); C && !(CB && &U == &CB->getCalledOperandUse() && calleeOf(*CB)))
        named(C, E, D, Done);
    }
    // A constant array that a call is given holds the addresses it holds, decision 0226.
    if (const auto *CB = dyn_cast<llvm::CallBase>(&I); CB && !isa<llvm::MemIntrinsic>(CB))
      for (const llvm::Value *Arg : CB->args())
        if (const auto *C = dyn_cast<llvm::Constant>(Arg); C && C->getType()->isPointerTy())
          addresses(C, false, E);
    if (const auto *Store = dyn_cast<llvm::StoreInst>(&I)) {
      access(Store->getPointerOperand(), true, E);
      stored(Store->getPointerOperand(), Store->getValueOperand(), E);
    } else if (const auto *Copy = dyn_cast<llvm::MemTransferInst>(&I)) {
      access(Copy->getRawDest(), true, E);
      access(Copy->getRawSource(), false, E);
      // A copy from a constant, such as the start value of `P x{&g_total, 2}`, stores what the constant holds.
      if (const auto *Source = dyn_cast<llvm::GlobalVariable>(Copy->getRawSource()->stripPointerCasts()); Source && Source->isConstant() && Source->hasInitializer())
        stored(Copy->getRawDest(), Source->getInitializer(), E);
    } else if (const auto *Load = dyn_cast<llvm::LoadInst>(&I)) {
      if (!Dispatch.count(Load))
        access(Load->getPointerOperand(), false, E);
    }
    else if (const auto *Rmw = dyn_cast<llvm::AtomicRMWInst>(&I))
      access(Rmw->getPointerOperand(), true, E);
    else if (const auto *Swap = dyn_cast<llvm::AtomicCmpXchgInst>(&I))
      access(Swap->getPointerOperand(), true, E);
    else if (const auto *CB = dyn_cast<llvm::CallBase>(&I))
      call(*CB, E, D);
    else if (const auto *Ret = dyn_cast<llvm::ReturnInst>(&I))
      escape(*Ret, E);
  }

  // A function that returns a reference or a pointer to a global lets its caller reach the global. The type of the return value says
  // how, as the type of a parameter does.
  // ponytail: only a global counts. The aliasing check refuses a reference from a function that the file does not define. Upgrade: refuse a
  // returned pointer whose root is a refusal here too.
  void escape(const llvm::ReturnInst &Ret, Effect &E) {
    if (!Ret.getReturnValue() || !Ret.getReturnValue()->getType()->isPointerTy())
      return;
    const FunctionDecl *FD = Fns.find(Ret.getFunction())->second.FD;
    std::vector<Root> Rs;
    Seen S;
    roots(Ret.getReturnValue(), Rs, S);
    for (const Root &R : Rs)
      if (R.K == Root::Global)
        reach(R, !FD || isMutableType(FD->getReturnType()), E);
  }

  // A store or a load. The roots of the pointer say what it reaches.
  void access(const llvm::Value *Pointer, bool Write, Effect &E) {
    std::vector<Root> Rs;
    Seen S;
    roots(Pointer, Rs, S);
    for (const Root &R : Rs)
      reach(R, Write, E);
  }

  void reach(const Root &R, bool Write, Effect &E) {
    if (R.K == Root::Global) {
      if (const auto Name = StateOf.find(cast<llvm::GlobalVariable>(R.V)); Name != StateOf.end())
        (Write ? E.Writes : E.Reads).insert(Name->second);
    } else if (R.K == Root::Refuse) {
      E.Refusals.insert(!R.Why.empty() ? R.Why
                                       : Write ? "global_state: a write through a pointer the gate cannot follow may reach any global, and no line can list it."
                                               : "global_state: a read through a pointer the gate cannot follow may reach any global, and no line can list it.");
    }
  }

  // The function is the library's own: a system header declares it, or it has no declaration, as the compiler's runtime has none.
  bool inLibrary(const llvm::Function *F) const {
    const FunctionDecl *FD = F ? Fns.find(F)->second.FD : nullptr;
    return !FD || Ctx->getSourceManager().isInSystemHeader(FD->getLocation());
  }

  // What a pointer reaches: the global, local or parameter at its root.
  // The result of a call reaches what the pointers given to the call reach, unless the gate cannot read the function.
  // A pointer that is loaded from memory points where the object that holds it says.
  // The gate follows it to the parameter or local that holds it, as the pointer in a std::vector or a vtable.
  // If a global that the file declares holds it, the pointee is not the global, and nothing can name it.
  // ponytail: a parameter that holds a pointer to a global hides the global from a read or a write through it. What the gate does count is the way in: a
  // store or a copy that puts the address of a global into memory is a change of the global, whether the address is a constant, a select or a phi of
  // addresses, or an element of a constant array of the compiler that a call is given (`stored` and `addresses`, decisions 0225 and 0226). A pointer
  // that comes from a call the gate cannot read is refused. A read of the global through such a pointer is not counted as a read. The rows raw_pointer,
  // lvalue_references and array_span ban such a pointer in the code that is judged. The row aliasing refuses a global that is passed to a call.
  // Upgrade: follow the object that holds the pointer, and count a write only for a write through it.
  // `Via` is the function that does the load, when the pointer was loaded.
  void roots(const llvm::Value *V, std::vector<Root> &Out, Seen &S, bool Loaded = false, const llvm::Function *Via = nullptr) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(V, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (!S.insert({O, Loaded}).second)
        continue;
      if (const auto *G = dyn_cast<llvm::GlobalVariable>(O)) {
        // A pointer in a global that the file declares may point at anything. So may one in a global of the library that user code reads.
        // One in a global that the tree does not know, such as a vtable, is the compiler's. The library reads its own.
        const bool Foreign = Known.count(G) || (Library.count(G) && !inLibrary(Via));
        Out.push_back({!Loaded ? Root::Global : Foreign ? Root::Refuse : Root::Local, O, ""});
      } else if (const auto *Load = dyn_cast<llvm::LoadInst>(O)) {
        roots(Load->getPointerOperand(), Out, S, true, Load->getFunction());
      } else if (isa<llvm::AllocaInst, llvm::Argument, llvm::ConstantPointerNull, llvm::UndefValue, llvm::LandingPadInst>(O)) {
        Out.push_back({Root::Local, O, ""});
      } else if (isa<llvm::Function>(O)) {
        Out.push_back({Root::Func, O, ""});
      } else if (const auto *Cast = dyn_cast<llvm::IntToPtrInst>(O)) {
        // A pointer that is made from a number, such as the function in a pointer to a member function, is where the number came from.
        roots(Cast->getOperand(0), Out, S, Loaded, Via);
      } else if (const auto *Extract = dyn_cast<llvm::ExtractValueInst>(O)) {
        roots(Extract->getAggregateOperand(), Out, S, Loaded, Via);
      } else if (const auto *Insert = dyn_cast<llvm::InsertValueInst>(O)) {
        roots(Insert->getAggregateOperand(), Out, S, Loaded, Via);
        roots(Insert->getInsertedValueOperand(), Out, S, Loaded, Via);
      } else if (const auto *CB = dyn_cast<llvm::CallBase>(O)) {
        const llvm::Function *F = calleeOf(*CB);
        const FunctionDecl *FD = F ? Fns.find(F)->second.FD : nullptr;
        // A function that the compiler wrote and a runtime function with no declaration are known.
        // So is an allocation function, which returns new memory that no other name reaches.
        const bool Readable = !F || !FD || !F->isDeclaration() || F->isIntrinsic() || F->returnDoesNotAlias() ||
                           FD->isReplaceableGlobalAllocationFunction() ||
                           ((inStdNamespace(FD) || inAbiNamespace(FD)) && Ctx->getSourceManager().isInSystemHeader(FD->getLocation()));
        if (!Readable) {
          Out.push_back({Root::Refuse, O,
                         "global_state: a reference from " + (FD ? FD->getNameAsString() : F->getName().str()) +
                             " may reach any global, and no line can list it."});
          continue;
        }
        for (const llvm::Value *A : CB->args())
          if (A->getType()->isPointerTy())
            roots(A, Out, S, Loaded, Via);
      } else {
        Out.push_back({Root::Refuse, O, ""});
      }
    }
  }

  void call(const llvm::CallBase &CB, Effect &E, Calls *D) {
    // ponytail: an inline assembly call brings nothing. The row inline_asm_intrinsics bans it, and no line could list what it does.
    if (CB.isInlineAsm())
      return;
    if (const auto *Mem = dyn_cast<llvm::MemIntrinsic>(&CB)) {
      access(Mem->getRawDest(), true, E);
      if (const auto *Copy = dyn_cast<llvm::MemTransferInst>(Mem))
        access(Copy->getRawSource(), false, E);
      return;
    }
    if (const llvm::Function *F = calleeOf(CB)) {
      direct(F, CB, E, D);
      return;
    }
    // An indirect call. First the virtual calls that the tree wrote at this place.
    // A method that has a body here brings its lines.
    // One that has none is read as a function with no body, as a direct call of it is.
    // It brings its lines, or it is refused when it has none.
    // ponytail: a virtual call brings the lines of the method that the source names.
    // The checks of overrides hold the overrides of this file to them, the ones with lines and the ones that nobody wrote.
    // An override in another file is not read. Upgrade: read every override of the hierarchy that the file can see.
    const auto &Virtuals = matched(CB);
    for (const VirtualCall *V : Virtuals) {
      arguments(V->Method, CB, E);
      E.add(hasBody(V->Method) ? linesOf(V->Method) : edge(V->Method));
      overridden(V->Method, E, D);
    }
    if (!Virtuals.empty())
      return;
    // A dispatch through a table that no virtual call of the tree explains has no callee that the gate can read.
    // A call through a pointer to a member function is one.
    if (!dispatchesOf(CB).empty()) {
      E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      return;
    }
    // Else a function that the caller passed, which the caller has accounted for, or a function that the callee value names.
    // A function that is loaded out of an object that a parameter or a local holds counts as passed, as every loaded pointer does. That is
    // sound because whoever stored the function address brought what the function does, `named` above.
    std::vector<Root> Rs;
    Seen S;
    roots(CB.getCalledOperand(), Rs, S);
    for (const Root &R : Rs) {
      if (R.K == Root::Func)
        direct(cast<llvm::Function>(R.V), CB, E, D);
      else if (R.K == Root::Local && isa<llvm::GlobalVariable>(R.V))
        table(cast<llvm::GlobalVariable>(R.V), CB, E, D);
      else if (R.K != Root::Local) {
        E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      }
    }
  }

  // A call through a pointer that is loaded from a global of the library. The library visits a variant through a table of function
  // pointers. The table is a constant, so the call may run any function that it names.
  // A global with no initializer in the module names none, and the call is refused.
  // This is for the indirect call only. A table of virtual functions is a constant too.
  // The store of its address in a constructor must not bring every virtual function to the constructor.
  void table(const llvm::GlobalVariable *G, const llvm::CallBase &CB, Effect &E, Calls *D) {
    if (!G->hasInitializer()) {
      E.Refusals.insert("global_state: a call through a pointer has no callee the gate can read.");
      return;
    }
    std::vector<const llvm::Function *> Functions;
    llvm::SmallPtrSet<const llvm::Constant *, 16> Done;
    functionsIn(G->getInitializer(), Functions, Done);
    for (const llvm::Function *F : Functions)
      direct(F, CB, E, D);
  }

  // What a virtual call brings besides the lines of the method that the source names.
  // It brings the code of the method, if nobody wrote it. The destructor that the compiler wrote is one, and it has no lines.
  // If a system header declares the method, no line can be asked of the library. Then it brings the code of every override in the module.
  // Every override is a body that the call may run, for the sequencing check.
  // ponytail: every override in the module counts, not only the ones that the object could be. Upgrade: follow the type of the object.
  void overridden(const CXXMethodDecl *Method, Effect &E, Calls *D) {
    const CXXMethodDecl *Canonical = cast<CXXMethodDecl>(Method->getCanonicalDecl());
    if (D)
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        D->Bodies.push_back(F);
    if (const auto Own = ByDecl.find(Canonical); Own != ByDecl.end() && Fns.find(Own->second)->second.Is == Role::Carrier)
      bring(Own->second, E, D);
    if (Ctx->getSourceManager().isInSystemHeader(Method->getLocation()))
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        bring(F, E, D);
  }

  void direct(const llvm::Function *F, const llvm::CallBase &CB, Effect &E, Calls *D) {
    if (F->isIntrinsic())
      return;
    const Fn &Info = Fns.find(F)->second;
    // The compiler's own runtime has no declaration, so no parameter to bind an argument to. With no body it brings nothing, and with one
    // it brings what its own code does.
    // ponytail: a function with a body and no declaration is trusted to touch no state through its arguments.
    if (!Info.FD) {
      if (!F->isDeclaration())
        bring(F, E, D);
      return;
    }
    arguments(Info.FD, CB, E);
    bring(F, E, D);
  }

  // The pointers a call is given. One that reaches a global writes it if the parameter it binds to can write, and reads it if not.
  void arguments(const FunctionDecl *FD, const llvm::CallBase &CB, Effect &E) {
    llvm::SmallVector<bool, 8> Mutable;
    if (FD) {
      if (const auto *Method = dyn_cast<CXXMethodDecl>(FD); Method && !Method->isStatic())
        Mutable.push_back(!Method->isConst());
      for (const ParmVarDecl *Parameter : FD->parameters())
        Mutable.push_back(isMutableType(Parameter->getType()));
    }
    // The arguments that the IR adds are no parameter.
    llvm::SmallVector<unsigned, 8> Real;
    for (unsigned I = 0; I < CB.arg_size(); ++I)
      if (!CB.paramHasAttr(I, llvm::Attribute::StructRet) && !CB.paramHasAttr(I, llvm::Attribute::InAlloca))
        Real.push_back(I);
    // ponytail: the arguments match the parameters in order. A parameter that the ABI splits in two, such as a std::span, or an argument
    // that is a variable argument, throws the order off. Then every pointer is as mutable as the most mutable parameter. Upgrade:
    // read the ABI's own list of arguments from clang.
    const bool Match = Real.size() == Mutable.size();
    const bool Any = llvm::any_of(Mutable, [](bool B) { return B; });
    for (unsigned K = 0; K < Real.size(); ++K) {
      const llvm::Value *A = CB.getArgOperand(Real[K]);
      // An argument by value is a copy, so it is no name.
      if (CB.paramHasAttr(Real[K], llvm::Attribute::ByVal) || !A->getType()->isPointerTy())
        continue;
      std::vector<Root> Rs;
      Seen S;
      roots(A, Rs, S);
      for (const Root &R : Rs)
        reach(R, Match ? Mutable[K] : Any, E);
    }
  }

  // ------------------------------------------------------------ places

  // Where an instruction is, from the debug line table. No file when it has no place.
  Place placeOf(const llvm::Instruction &I) {
    const llvm::DebugLoc &DL = I.getDebugLoc();
    if (!DL || !DL.getLine())
      return {};
    const llvm::DIFile *File = DL->getFile();
    auto Found = Files.find(File);
    if (Found == Files.end()) {
      llvm::SmallString<256> Path(File->getFilename());
      if (!llvm::sys::path::is_absolute(Path))
        Path = (File->getDirectory() + "/" + File->getFilename()).str();
      const auto Entry = Ctx->getSourceManager().getFileManager().getOptionalFileRef(Path);
      Found = Files.try_emplace(File, Entry ? &Entry->getFileEntry() : nullptr).first;
    }
    return {Found->second, DL.getLine(), DL.getCol() ? DL.getCol() : 1};
  }

  // Where an instruction is in the tree: the debug line table, turned back into a location. An instruction with no place is at its
  // function.
  SourceLocation locationOf(const llvm::Instruction &I, const FunctionDecl *FD) {
    if (const Place P = placeOf(I); P.File) {
      const SourceLocation Loc = Ctx->getSourceManager().translateFileLineCol(P.File, P.Line, P.Col);
      if (Loc.isValid())
        return Loc;
    }
    return FD ? FD->getLocation() : SourceLocation();
  }

  // ------------------------------------------------------------ plain code, decision 0047

  // A function of the file, for the gate's kinds: one it defines, and the call operator of a lambda it writes. Such a function has its own
  // kind and its own calls, so a walk from a call stops at it. Anything else in the module is code the file did not write, and a walk
  // goes through it: the library, and the members that the compiler writes.
  bool written(const Fn &Info) const {
    if (Info.Is == Role::Judged)
      return true;
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Info.FD);
    return Info.Is == Role::Carrier && Method && isLambdaCallOperator(Method) && !Ctx->getSourceManager().isInSystemHeader(Method->getLocation());
  }

  // The functions that an instruction names, in the module: the callee of a direct call, each function that a virtual call can reach, and
  // each function constant among the operands, as a table of function pointers is. This is what `instruction` and `call` bring, as a
  // list of functions.
  // A virtual call reaches the method that the source names, and every override in the module: one that the file wrote, one that the
  // compiler wrote, such as the destructor of a derived class, and one of a class template over a base that it takes as a parameter.
  // ponytail: a virtual call inside the library has no call in the tree, so the overrides it can reach are not read. Upgrade: the type of
  // the object.
  void namedBy(const llvm::Instruction &I, std::vector<const llvm::Function *> &Out) {
    llvm::SmallPtrSet<const llvm::Constant *, 8> Done;
    const auto *CB = dyn_cast<llvm::CallBase>(&I);
    for (const llvm::Use &U : I.operands())
      if (const auto *C = dyn_cast<llvm::Constant>(U.get()); C && !(CB && &U == &CB->getCalledOperandUse() && calleeOf(*CB)))
        functionsIn(C, Out, Done);
    if (!CB || CB->isInlineAsm() || isa<llvm::MemIntrinsic>(CB))
      return;
    if (const llvm::Function *F = calleeOf(*CB)) {
      if (!F->isIntrinsic())
        Out.push_back(F);
      return;
    }
    const auto &Virtual = matched(*CB);
    for (const VirtualCall *V : Virtual) {
      const CXXMethodDecl *Canonical = cast<CXXMethodDecl>(V->Method->getCanonicalDecl());
      if (const auto Own = ByDecl.find(Canonical); Own != ByDecl.end())
        Out.push_back(Own->second);
      for (const llvm::Function *F : Overriders.lookup(Canonical))
        Out.push_back(F);
    }
    if (!Virtual.empty() || !dispatchesOf(*CB).empty())
      return;
    std::vector<Root> Rs;
    Seen S;
    roots(CB->getCalledOperand(), Rs, S);
    for (const Root &R : Rs) {
      if (R.K == Root::Func) {
        Out.push_back(cast<llvm::Function>(R.V));
      } else if (const auto *G = dyn_cast<llvm::GlobalVariable>(R.V); R.K == Root::Local && G && G->hasInitializer()) {
        llvm::SmallPtrSet<const llvm::Constant *, 16> Visited;
        functionsIn(G->getInitializer(), Out, Visited);
      }
    }
  }

  // Every call of a function of the file, and of the code that starts the globals, that runs a plain function. A plain function is one
  // that the file defines or declares, or a member that the compiler writes for a plain class, decision 0051. The code in the module that
  // the file did not write is followed until it reaches one. The
  // plain functions that each such piece of code can run are found once, by a fixpoint like the one for the effects.
  void plainCode() {
    llvm::DenseSet<const llvm::Function *> Plain;
    for (const auto &[F, Info] : Fns)
      if (Info.FD && (Info.Is == Role::Edge || written(Info) || Info.FD->isImplicit()) &&
          insidePlain(Info.FD->getDefinition() ? Info.FD->getDefinition() : Info.FD))
        Plain.insert(F);
    if (Plain.empty())
      return;
    struct Runs {
      std::set<const llvm::Function *> Plain, Next;
    };
    llvm::DenseMap<const llvm::Function *, Runs> Of;
    std::vector<const llvm::Function *> Named;
    for (const auto &[F, Info] : Fns) {
      if (Info.Is != Role::Carrier || written(Info))
        continue;
      Runs &R = Of[F];
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named) {
            const Fn &Callee = Fns.find(G)->second;
            if (Plain.count(G))
              R.Plain.insert(G);
            else if (Callee.Is == Role::Carrier && !written(Callee))
              R.Next.insert(G);
          }
        }
    }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (auto &[F, R] : Of)
        for (const llvm::Function *Dep : R.Next)
          if (Dep != F) {
            const auto &Up = Of.find(Dep)->second.Plain;
            const size_t Before = R.Plain.size();
            R.Plain.insert(Up.begin(), Up.end());
            Changed |= R.Plain.size() != Before;
          }
    }
    // The code that starts the globals has no declaration, and it runs what the file wrote.
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge || !(written(Info) || !Info.FD))
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named) {
            if (Plain.count(G))
              plainCall(I, Info.FD, G);
            else if (const auto Up = Of.find(G); Up != Of.end())
              for (const llvm::Function *P : Up->second.Plain)
                plainCall(I, Info.FD, P);
          }
        }
    }
  }

  // The code that starts a global has no place of its own, so its call stands at the variable that it starts.
  // ponytail: the first variable of the user's files that the code names. Upgrade: the variable that the call is for.
  SourceLocation globalStarted(const llvm::Function &F) const {
    for (const llvm::BasicBlock &BB : F)
      for (const llvm::Instruction &I : BB)
        for (const llvm::Use &U : I.operands())
          if (const auto *G = dyn_cast<llvm::GlobalVariable>(U.get()))
            if (const auto Var = VarOf.find(G); Var != VarOf.end() && !Ctx->getSourceManager().isInSystemHeader(Var->second->getLocation()))
              return Var->second->getLocation();
    return {};
  }

  // Where a call of a function of the file stands, as a place in a file. None when the call has no place.
  SourceLocation callPlace(const llvm::Instruction &I, const FunctionDecl *Holder) {
    SourceLocation Loc = locationOf(I, Holder);
    if (Loc.isInvalid() && !Holder)
      Loc = globalStarted(*I.getFunction());
    return Loc.isInvalid() ? Loc : Ctx->getSourceManager().getExpansionLoc(Loc);
  }

  void plainCall(const llvm::Instruction &I, const FunctionDecl *Holder, const llvm::Function *Plain) {
    const SourceLocation At = callPlace(I, Holder);
    if (At.isInvalid())
      return;
    const std::string Name = patternOf(Fns.find(Plain)->second.FD)->getQualifiedNameAsString();
    if (PlainSeen.insert({At.getRawEncoding(), Name}).second)
      PlainCalls.push_back({At, Name});
  }

  // ------------------------------------------------------------ indirect calls, decisions 0048 and 0049

  // Whether the contents of a piece of memory are named: the pointer is read from a constant table, or from a local object that holds
  // nothing but named values. Memory that a parameter, a call or a global that can change gives has no name.
  // A call of code that the file did not write can hand out a place in a table that its caller gave, as the library does to find the
  // function for a pair of variants. The place is then the one that the call was given: the pointer that it returns comes from its
  // parameter or from a constant table, and the walk follows it into the call. `Frames` are the calls that the walk is inside.
  bool namesMemory(const llvm::Value *Pointer, llvm::SmallPtrSetImpl<const llvm::Value *> &Done,
                   llvm::SmallVectorImpl<const llvm::CallBase *> &Frames) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(Pointer, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (const auto *G = dyn_cast<llvm::GlobalVariable>(O)) {
        if (!G->isConstant() || !G->hasInitializer())
          return false;
      } else if (isa<llvm::AllocaInst>(O)) {
        if (!Frames.empty() || (Done.insert(O).second && !namesLocal(O, Done)))
          return false;
      } else if (const auto *Parameter = dyn_cast<llvm::Argument>(O)) {
        if (Frames.empty())
          return false;
        const llvm::CallBase *Call = Frames.pop_back_val();
        const bool Named = namesMemory(Call->getArgOperand(Parameter->getArgNo()), Done, Frames);
        Frames.push_back(Call);
        if (!Named)
          return false;
      } else if (const auto *Call = dyn_cast<llvm::CallBase>(O)) {
        const llvm::Function *Callee = calleeOf(*Call);
        if (!Callee || Callee->isDeclaration() || written(Fns.find(Callee)->second) || !Done.insert(Call).second)
          return false;
        Frames.push_back(Call);
        for (const llvm::BasicBlock &BB : *Callee)
          if (const auto *Ret = dyn_cast<llvm::ReturnInst>(BB.getTerminator()))
            if (!Ret->getReturnValue() || !namesMemory(Ret->getReturnValue(), Done, Frames))
              return false;
        Frames.pop_back();
      } else {
        return false;
      }
    }
    return true;
  }

  // Whether a local object holds named values only. Every store into it and every copy into it brings a named value. Its address stays
  // here: a call that gets the address can store any pointer in it, and so can anything that keeps the address.
  bool namesLocal(const llvm::Value *Slot, llvm::SmallPtrSetImpl<const llvm::Value *> &Done) {
    llvm::SmallVector<const llvm::CallBase *, 1> NoFrames;
    llvm::SmallVector<const llvm::Value *, 8> Work{Slot};
    llvm::SmallPtrSet<const llvm::Value *, 8> Derived{Slot};
    while (!Work.empty()) {
      const llvm::Value *P = Work.pop_back_val();
      for (const llvm::User *U : P->users()) {
        if (isa<llvm::LoadInst, llvm::ICmpInst>(U))
          continue;
        if (const auto *Store = dyn_cast<llvm::StoreInst>(U)) {
          if (Store->getValueOperand() == P || !namesAll(Store->getValueOperand(), Done))
            return false;
        } else if (const auto *Copy = dyn_cast<llvm::MemTransferInst>(U)) {
          if (Copy->getRawDest() == P && !namesMemory(Copy->getRawSource(), Done, NoFrames))
            return false;
        } else if (const auto *Intrinsic = dyn_cast<llvm::IntrinsicInst>(U)) {
          if (!isa<llvm::MemSetInst, llvm::DbgInfoIntrinsic>(Intrinsic) && !Intrinsic->isLifetimeStartOrEnd())
            return false;
        } else if (isa<llvm::GetElementPtrInst, llvm::BitCastInst, llvm::AddrSpaceCastInst, llvm::PHINode, llvm::SelectInst>(U)) {
          if (Derived.insert(U).second)
            Work.push_back(U);
        } else {
          return false;
        }
      }
    }
    return true;
  }

  // Whether each value that can reach `V` is named, decision 0049: a function constant, or a pointer read from memory that is named. A
  // parameter, `this`, the result of a call, a return slot and a pointer of a global that can change have no name. A virtual call and a
  // table of decision 0037 are named by their vtables and their constants, and the caller does not ask about them.
  bool namesAll(const llvm::Value *V, llvm::SmallPtrSetImpl<const llvm::Value *> &Done) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(V, Objects, nullptr, 0);
    for (const llvm::Value *O : Objects) {
      if (!Done.insert(O).second)
        continue;
      if (isa<llvm::Constant>(O) && !isa<llvm::GlobalVariable>(O))
        continue;
      if (const auto *Load = dyn_cast<llvm::LoadInst>(O)) {
        llvm::SmallVector<const llvm::CallBase *, 4> Frames;
        if (!namesMemory(Load->getPointerOperand(), Done, Frames))
          return false;
      } else if (const auto *Extract = dyn_cast<llvm::ExtractValueInst>(O)) {
        if (!namesAll(Extract->getAggregateOperand(), Done))
          return false;
      } else if (const auto *Insert = dyn_cast<llvm::InsertValueInst>(O)) {
        if (!namesAll(Insert->getAggregateOperand(), Done) || !namesAll(Insert->getInsertedValueOperand(), Done))
          return false;
      } else if (const auto *Cast = dyn_cast<llvm::IntToPtrInst>(O)) {
        if (!namesAll(Cast->getOperand(0), Done))
          return false;
      } else {
        return false;
      }
    }
    return true;
  }

  // An indirect call that is no virtual call, and that has no name. The dispatch of a virtual call reads a vtable, and the tree names the
  // method. A dispatch that no call of the tree explains is a pointer to a member function, which the row already refuses.
  bool unnamedCall(const llvm::CallBase &CB) {
    if (CB.isInlineAsm() || isa<llvm::MemIntrinsic>(CB) || calleeOf(CB) || !matched(CB).empty() || !dispatchesOf(CB).empty())
      return false;
    llvm::SmallPtrSet<const llvm::Value *, 16> Done;
    return !namesAll(CB.getCalledOperand(), Done);
  }

  // Every call of a function of the file, and of the code that starts the globals, that runs an indirect call with no name. It makes the
  // call itself, or it runs code that the file did not write and that makes it. The row `function_pointers` judges that call. A pointer
  // is named by constants alone, so a pointer that a parameter holds, or a call gave, or a call can write, has no name, and a verified
  // function that calls through it is refused. A trusted body may hold such a pointer, and the core drops the finding there.
  // ponytail: the walk of a local object reads its stores and its copies. Any other use of the address is a call, and the object has no
  // name from then on, whatever the call does with it. A pointer in a global that can change has no name either. Upgrade: read what the
  // call may store, from the lowered form of its body.
  void indirectCode() {
    // The code that the file did not write and that has an unnamed indirect call, by a fixpoint like the one for the plain functions.
    llvm::DenseSet<const llvm::Function *> Unnamed;
    llvm::DenseMap<const llvm::Function *, std::vector<const llvm::Function *>> Next;
    std::vector<const llvm::Function *> Named;
    for (const auto &[F, Info] : Fns) {
      if (Info.Is != Role::Carrier || written(Info))
        continue;
      auto &Mine = Next[F];
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          if (const auto *CB = dyn_cast<llvm::CallBase>(&I); CB && unnamedCall(*CB))
            Unnamed.insert(F);
          Named.clear();
          namedBy(I, Named);
          for (const llvm::Function *G : Named)
            if (const Fn &Callee = Fns.find(G)->second; Callee.Is == Role::Carrier && !written(Callee))
              Mine.push_back(G);
        }
    }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &[F, Callees] : Next)
        if (!Unnamed.count(F) && llvm::any_of(Callees, [&](const llvm::Function *G) { return Unnamed.count(G); }))
          Changed |= Unnamed.insert(F).second;
    }
    for (const auto &[F, Info] : Fns) {
      if (Info.Is == Role::Edge || !(written(Info) || !Info.FD))
        continue;
      for (const llvm::BasicBlock &BB : *F)
        for (const llvm::Instruction &I : BB) {
          const auto *CB = dyn_cast<llvm::CallBase>(&I);
          bool Found = CB && unnamedCall(*CB);
          if (!Found) {
            Named.clear();
            namedBy(I, Named);
            Found = llvm::any_of(Named, [&](const llvm::Function *G) { return Unnamed.count(G); });
          }
          if (!Found)
            continue;
          if (const SourceLocation At = callPlace(I, Info.FD); At.isValid() && IndirectSeen.insert(At.getRawEncoding()).second)
            IndirectCalls.push_back(At);
        }
    }
  }

  // ------------------------------------------------------------ judging

  // The function is judged on its own instructions, against its own lines. The module may hold it twice, as the variants of a constructor
  // or a destructor are, and each is judged. `Reported` keeps one finding for a line and a message.
  void judge(const llvm::Function &F, const FunctionDecl *FD) {
    const SourceManager &SM = Ctx->getSourceManager();
    const Effect Own = linesOf(FD);
    enum Kind { Write, Read, Refusal };
    struct Item {
      SourceLocation Loc;
      Kind K;
      std::string Text;
    };
    std::vector<Item> Items;
    for (const llvm::BasicBlock &BB : F)
      for (const llvm::Instruction &I : BB) {
        Effect E;
        instruction(I, E, nullptr);
        if (!E.size())
          continue;
        const SourceLocation Loc = locationOf(I, FD);
        for (const std::string &Name : E.Writes)
          if (!Own.Writes.count(Name))
            Items.push_back({Loc, Write, Name});
        for (const std::string &Name : E.Reads)
          if (!Own.Writes.count(Name) && !Own.Reads.count(Name))
            Items.push_back({Loc, Read, Name});
        for (const std::string &Message : E.Refusals)
          Items.push_back({Loc, Refusal, Message});
      }
    const auto Line = [&](SourceLocation Loc) { return std::make_pair(SM.getFileID(Loc).getHashValue(), SM.getExpansionLineNumber(Loc)); };
    // Where a line writes a name and reads it too, the write is the finding.
    std::set<std::pair<std::pair<unsigned, unsigned>, std::string>> Written;
    for (const Item &It : Items)
      if (It.K == Write)
        Written.insert({Line(It.Loc), It.Text});
    for (const Item &It : Items) {
      if (It.K == Read && Written.count({Line(It.Loc), It.Text}))
        continue;
      const std::string Message = It.K == Write  ? "global_state: " + It.Text + " changes, and the modifies line does not list it."
                                  : It.K == Read ? "global_state: " + It.Text + " is read, and no reads or modifies line lists it."
                                                 : It.Text;
      report(It.Loc, Message);
    }
  }
};

// One table for the translation unit. It is never freed at exit: the libraries it holds may be gone by then.
Lowered *Table = nullptr;
// Whether some check has asked for the matchers of the table in this translation unit. One does, whichever checks are on.
bool TableMatchers = false;
Lowered &table() {
  if (!Table)
    Table = new Lowered;
  return *Table;
}
} // namespace

void startTable() {
  delete Table;
  Table = nullptr;
  TableMatchers = false;
}
bool tableChanges(const FunctionDecl *Callee) { return table().changes(Callee); }
void giveTable(ASTContext *Context) { table().use(Context); }

namespace {

// The method that a call or a delete reaches through the vtable, as the source says it, or null.
const CXXMethodDecl *virtualTarget(const Stmt *S) {
  if (const auto *Call = dyn_cast<CallExpr>(S)) {
    const auto *Method = dyn_cast_or_null<CXXMethodDecl>(Call->getCalleeDecl());
    // A call with a qualifier names the function, and the call is no virtual one.
    const auto *Member = dyn_cast<MemberExpr>(Call->getCallee()->IgnoreParens());
    return Method && Method->isVirtual() && !(Member && Member->hasQualifier()) ? Method : nullptr;
  }
  if (const auto *Delete = dyn_cast<CXXDeleteExpr>(S)) {
    // A delete of an object with a virtual destructor calls it through the vtable.
    const QualType Destroyed = Delete->getDestroyedType();
    const CXXRecordDecl *Class = Destroyed.isNull() ? nullptr : Destroyed->getAsCXXRecordDecl();
    const CXXDestructorDecl *Destructor = Class && Class->hasDefinition() ? Class->getDestructor() : nullptr;
    return Destructor && Destructor->isVirtual() ? Destructor : nullptr;
  }
  return nullptr;
}

// The virtual calls inside a default argument. The compiler puts the code of a default argument on the line of the call that uses it.
// So they are recorded with the range of that call, and the function that holds that call.
void collectDefault(const Stmt *S, SourceRange Where, const FunctionDecl *Owner) {
  if (!S)
    return;
  if (const CXXMethodDecl *Method = virtualTarget(S))
    table().addVirtual(Where, Method, Owner);
  if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(S))
    collectDefault(Default->getExpr(), Where, Owner);
  else if (const auto *Init = dyn_cast<CXXDefaultInitExpr>(S))
    collectDefault(Init->getExpr(), Where, Owner);
  else
    for (const Stmt *Child : S->children())
      collectDefault(Child, Where, Owner);
}

} // namespace

void registerTableMatchers(MatchFinder *Finder, MatchFinder::MatchCallback *Callback) {
  if (TableMatchers)
    return;
  TableMatchers = true;
  // The function that holds the expression, which tells the same line of two functions apart. A default member initializer has none: its
  // code runs in every function that makes the object.
  const auto Holder = optionally(allOf(unless(hasAncestor(fieldDecl())), forFunction(functionDecl().bind("owner"))));
  const auto Defaulted = hasAnyArgument(ignoringImplicit(cxxDefaultArgExpr()));
  Finder->addMatcher(functionDecl(isDefinition(), unless(isExpansionInSystemHeader()), unless(notJudged())).bind("judged"), Callback);
  Finder->addMatcher(functionDecl(isDefinition(), isTemplateInstantiation()).bind("instance"), Callback);
  Finder->addMatcher(varDecl(isDefinition(), hasGlobalStorage(), isTemplateInstantiation()).bind("varinstance"), Callback);
  Finder->addMatcher(stmt(anyOf(callExpr(callee(cxxMethodDecl(isVirtual()))), cxxDeleteExpr()), Holder).bind("virtual"), Callback);
  Finder->addMatcher(stmt(anyOf(callExpr(Defaulted), cxxConstructExpr(Defaulted)), Holder).bind("defaulted"), Callback);
}

bool collectForTable(const MatchFinder::MatchResult &Result) {
  Lowered &T = table();
  const SourceManager &SM = *Result.SourceManager;
  const auto *Owner = Result.Nodes.getNodeAs<FunctionDecl>("owner");
  if (const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("judged")) {
    T.Judged.push_back(Function);
  } else if (const auto *Function = Result.Nodes.getNodeAs<FunctionDecl>("instance")) {
    T.Instances.push_back(Function);
  } else if (const auto *Var = Result.Nodes.getNodeAs<VarDecl>("varinstance")) {
    T.VarInstances.push_back(Var);
  } else if (const auto *Node = Result.Nodes.getNodeAs<Stmt>("virtual")) {
    if (const CXXMethodDecl *Method = virtualTarget(Node))
      T.addVirtual(SM.getExpansionRange(Node->getSourceRange()).getAsRange(), Method, Owner);
  } else if (const auto *Node = Result.Nodes.getNodeAs<Stmt>("defaulted")) {
    const SourceRange Where = SM.getExpansionRange(Node->getSourceRange()).getAsRange();
    const auto Each = [&](auto Arguments) {
      for (const Expr *Argument : Arguments)
        if (const auto *Default = dyn_cast<CXXDefaultArgExpr>(Argument->IgnoreImplicit()))
          collectDefault(Default->getExpr(), Where, Owner);
    };
    if (const auto *Call = dyn_cast<CallExpr>(Node))
      Each(Call->arguments());
    else
      Each(cast<CXXConstructExpr>(Node)->arguments());
  } else {
    return false;
  }
  return true;
}

namespace {

// cplusp-unlisted-state: decisions 0035, 0036 and 0037. A function writes only the global state its `//@ modifies` line lists.
// It reads only what its `//@ reads` or `modifies` line lists.
// State is a mutable global or static data member that a system header does not declare.
// The check judges the code that clang generates for the function, not the tree.
// A store is a write, a load is a read, and a call brings what its callee lists or what the callee's own code does.
// A call of a function that the gate cannot read is refused. So is a reference from a function this file does not define.
// Any global may be behind it, and no line can list that.
// The message is `global_state: {sentence}`, one finding per message per line.
// The pattern of a template is not judged. Its instantiations are.
class UnlistedStateCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    // The translation unit, so that the check runs once at least and has the context.
    Finder->addMatcher(translationUnitDecl(), this);
    registerTableMatchers(Finder, this);
    Finder->addMatcher(cxxMethodDecl(unless(isExpansionInSystemHeader()), unless(isImplicit())).bind("method"), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    if (const auto *Method = Result.Nodes.getNodeAs<CXXMethodDecl>("method"))
      if (Method == Method->getCanonicalDecl())
        checkOverride(Method, *Result.SourceManager);
  }
  void onEndOfTranslationUnit() override {
    for (const Finding &F : table().findings())
      diag(F.Loc, "%0") << StringRef(F.Message);
  }

private:
  // An override lists no more than the function it overrides, so that a call through the base brings lines that hold for every override.
  void checkOverride(const CXXMethodDecl *Method, const SourceManager &SM) {
    if (Method->size_overridden_methods() == 0)
      return;
    const Contract Own = contractOf(SM, Method);
    const auto &State = table().state();
    for (const CXXMethodDecl *Direct : Method->overridden_methods())
      for (const CXXMethodDecl *Base : lineHolders(Direct)) {
        const Contract Up = contractOf(SM, Base);
        const std::set<std::string> UpWrites = namedState(Up.Modifies, State, Up.Parameters), UpReads = namedState(Up.Reads, State, Up.Parameters);
        for (const std::string &Var : namedState(Own.Modifies, State, Own.Parameters))
          if (!UpWrites.count(Var))
            diag(Method->getLocation(), "global_state: %0 changes %1, and the modifies line of %2 does not list it.")
                << Method->getNameAsString() << StringRef(Var) << Base->getQualifiedNameAsString();
        for (const std::string &Var : namedState(Own.Reads, State, Own.Parameters))
          if (!UpWrites.count(Var) && !UpReads.count(Var))
            diag(Method->getLocation(), "global_state: %0 reads %1, and no reads or modifies line of %2 lists it.")
                << Method->getNameAsString() << StringRef(Var) << Base->getQualifiedNameAsString();
      }
  }
};

// cplusp-line-directive: decision 0037. Every `#line` and every line marker that the preprocessor processed, under the build's own flags.
// The preprocessor holds them in the line table of the source manager.
// The entry sits in the directive's line. So the finding sits at the first column of that line, before the directive.
// A marker may declare the rest of its file a system header, which clang-tidy does not judge.
// The entry that `#pragma GCC system_header` adds is no directive. The check `cplusp-pragma` reports the pragma.
// The preprocessor tells where it made one. No other entry is skipped, so `# 3 "this file" 3` is a finding.
// A NOLINT on the line of a directive suppresses this finding. The gate reports the NOLINT, and that stands.
// ponytail: the entry sits on the line of the number. A directive that a comment spreads over lines is reported on the line of its
// number, not of its `#`. Upgrade: a callback of the preprocessor for each directive.
class LineDirectiveCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(translationUnitDecl(), this); }
  void registerPPCallbacks(const SourceManager &, Preprocessor *PP, Preprocessor *) override {
    // The gate runs one clang-tidy over every file, and each unit has its own offsets.
    Pragmas.clear();
    PP->addPPCallbacks(std::make_unique<PragmaNotes>(Pragmas));
  }
  void check(const MatchFinder::MatchResult &Result) override { SM = Result.SourceManager; }
  void onEndOfTranslationUnit() override {
    if (!SM)
      return;
    LineTableInfo &Lines = SM->getLineTable();
    for (const auto &[File, Entries] : Lines) {
      // The predefined macros are a buffer that holds line markers of its own, and no file of the user's.
      if (!SM->getFileEntryForID(File))
        continue;
      const StringRef Text = SM->getBufferData(File);
      const auto Offset = [&](unsigned Line) { return SM->getFileOffset(SM->translateLineCol(File, Line, 1)); };
      for (const LineEntry &Entry : Entries) {
        unsigned Line = SM->getLineNumber(File, Entry.FileOffset);
        const SourceLocation Own = SM->translateLineCol(File, Line, 1);
        if (SM->isInSystemHeader(Own) || Pragmas.count(SM->getLocForStartOfFile(File).getLocWithOffset(Entry.FileOffset).getRawEncoding()))
          continue;
        // A line splice joins the lines of a directive, and the `#` is on the first of them.
        while (Line > 1 && Text.slice(Offset(Line - 1), Offset(Line)).rtrim().ends_with("\\"))
          --Line;
        diag(SM->translateLineCol(File, Line, 1), "line directive: not allowed in verified code. It moves the gate's view.");
      }
    }
  }

private:
  // Where the preprocessor made a line table entry for a `system_header` pragma.
  struct PragmaNotes : PPCallbacks {
    std::set<SourceLocation::UIntTy> &Where;
    explicit PragmaNotes(std::set<SourceLocation::UIntTy> &Where) : Where(Where) {}
    void FileChanged(SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind, FileID) override {
      if (Reason == SystemHeaderPragma)
        Where.insert(Loc.getRawEncoding());
    }
  };
  SourceManager *SM = nullptr;
  std::set<SourceLocation::UIntTy> Pragmas;
};

// A finding of the gate's own at `At`, which is a place in a file. The message is the presumed place, then the sentence, set apart by tabs.
// The pragma check and the marker check report this way. The gate reads the line from the message and maps the finding to its rule.
// A tab or a line break in the sentence would move the cut of the gate, so each becomes a space. A sentence can hold the text of the source.
void reportAt(ClangTidyCheck &Check, const SourceManager &SM, SourceLocation At, const std::string &Sentence) {
  const PresumedLoc Place = SM.getPresumedLoc(At);
  std::string Clean = Sentence;
  std::replace_if(Clean.begin(), Clean.end(), [](char C) { return C == '\t' || C == '\n' || C == '\r'; }, ' ');
  if (Place.isValid())
    Check.diag(At, "%0") << StringRef(std::string(Place.getFilename()) + "\t" + std::to_string(Place.getLine()) + "\t" + Clean);
}

// cplusp-pragma: decision 0038. Every `#pragma`, `_Pragma` and `__pragma` that the preprocessor reads, under the build's own flags.
// It also refuses a header name with a backslash. The compiler reads such a name its own way, and the dependency list prints it as a slash.
// The preprocessor says when it starts one, before any handler runs. So a raw string that looks like a pragma is no pragma.
// The gate reads no compiler output that holds source text. A pragma in a system header is the library's own.
// The finding of a `#pragma` sits at the end of its first word, in the file that holds it. The pragma's own line is still a user line.
// A header turns system from the next line on, and that is after this callback.
// A `system_header` pragma in the main file is a finding too. Clang ignores it there, and it is still not allowed.
// The message is the presumed file, the presumed line and the sentence for the bot, set apart by tabs.
// A `#line` moves the presumed place, and the finding shows the place that the author gave.
// A NOLINT on the line of a pragma or an include suppresses the finding of this check. The gate reports the NOLINT, and that stands.
// A diagnostic pragma in a system header may change the warnings of the code that includes it.
// The compiler keeps the state of every warning, with its pushes and pops. So the check asks it, and keeps no count of its own.
// The preprocessor enters a system header from a file that is none. The check asks the level of each warning that the policy enforces,
// at the include. The header ends and the file resumes. The check asks again at the place where the file resumes.
// A warning that was on and is off is the finding. User code cannot change a warning, because every pragma in it is refused.
// The finding sits at the include that brought the outermost header in.
// When that include is no file, as with `-include`, it sits at the start of the main file.
// A header that pushes and pops around its change, as libstdc++ does, stays quiet.
// ponytail: the words come from the source, read by the compiler's lexer at the introducer. A `__pragma` expands macros first.
// So the words of a `__pragma` may not be the ones that run. Only a `#pragma` is `once` for the gate, which reads no more than that.
// The diagnostic pragmas that run are reported by their own callbacks, whatever the words said. Another pragma that a macro makes
// is still a finding, and its sentence names the source words. Upgrade: read the tokens that the handler reads.
// Reading them ahead with a backtrack in the callback changes the build. A macro in the pragma is no longer expanded.
// A pragma that nobody knows leaves its words to the parser.
class PragmaCheck : public ClangTidyCheck {
public:
  // The base class keeps the context private, so the check keeps its own pointer.
  PragmaCheck(StringRef Name, ClangTidyContext *Context) : ClangTidyCheck(Name, Context), Ctx(Context) {}
  void registerPPCallbacks(const SourceManager &SM, Preprocessor *PP, Preprocessor *) override {
    // The driver turns `-include h.h` into `-include-pch h.h.pch` when that file sits beside the header. The compiler tells it.
    if (!PP->getPreprocessorOpts().ImplicitPCHInclude.empty())
      refusePrecompiled(*this, SM);
    PP->addPPCallbacks(std::make_unique<Notes>(*this, *Ctx, SM, *PP));
  }
  void registerMatchers(MatchFinder *Finder) override { Finder->addMatcher(translationUnitDecl(), this); }
  // A precompiled header and a module are read by the AST reader, whichever way the build came to load one.
  // clang-tidy gives every run a reader, and it holds no file until a precompiled header or a module is loaded.
  // An external source of any other kind is refused too.
  void check(const MatchFinder::MatchResult &Result) override {
    ExternalASTSource *Source = Result.Context->getExternalSource();
    if (Source && (!isa<ASTReader>(Source) || cast<ASTReader>(Source)->getModuleManager().size()))
      refusePrecompiled(*this, *Result.SourceManager);
  }

private:
  ClangTidyContext *Ctx;

  // Precompiled state carries what an earlier run of the compiler read, and the gate did not see it. The finding sits at the start of
  // the main file. Both ways of finding it report the same place and the same words, and the diagnostics engine keeps one.
  static void refusePrecompiled(ClangTidyCheck &Check, const SourceManager &SM) {
    reportAt(Check, SM, SM.getLocForStartOfFile(SM.getMainFileID()),
             "include: a precompiled header is loaded. It carries state from an earlier run of the compiler.");
  }

  struct Notes : PPCallbacks {
    ClangTidyCheck &Check;
    ClangTidyContext &Context;
    const SourceManager &SM;
    Preprocessor &PP;
    // Whether the `#pragma` that started last was already reported as a diagnostic pragma, so that its callback does not report it twice.
    bool DiagnosticSeen = false;
    // The files that are being read. A system header entered from a file that is none holds the levels of the warnings.
    // They are the warnings that the policy enforces, as they were at its include.
    struct Frame {
      bool System = false;
      bool Outermost = false;
      std::vector<bool> Enforced;
    };
    std::vector<Frame> Frames;
    unsigned SystemFrames = 0;
    // The warnings that the policy enforces: those whose `clang-diagnostic-{name}` check is on in this run. Found once.
    std::vector<unsigned> Enforced;
    bool EnforcedKnown = false;
    Notes(ClangTidyCheck &Check, ClangTidyContext &Context, const SourceManager &SM, Preprocessor &PP)
        : Check(Check), Context(Context), SM(SM), PP(PP) {}

    void report(SourceLocation At, const std::string &Sentence) { reportAt(Check, SM, At, Sentence); }

    // A diagnostic pragma that the preprocessor runs, whatever words said that it would.
    void diagnostic(SourceLocation Loc) {
      const SourceLocation At = SM.getExpansionLoc(Loc);
      if (!DiagnosticSeen && At.isValid() && !SM.isInSystemHeader(At))
        report(At, "pragma diagnostic: not allowed in verified code. It silences the gate.");
    }

    const std::vector<unsigned> &enforced() {
      if (!EnforcedKnown) {
        EnforcedKnown = true;
        std::vector<diag::kind> All;
        DiagnosticIDs::getAllDiagnostics(diag::Flavor::WarningOrError, All);
        for (const unsigned ID : All) {
          const StringRef Option = DiagnosticIDs::getWarningOptionForDiag(ID);
          if (!Option.empty() && Context.isCheckEnabled(("clang-diagnostic-" + Option).str()))
            Enforced.push_back(ID);
        }
      }
      return Enforced;
    }

    // Which of the warnings that the policy enforces are on at `At`.
    std::vector<bool> levels(SourceLocation At) {
      std::vector<bool> On;
      for (const unsigned ID : enforced())
        On.push_back(PP.getDiagnostics().getDiagnosticLevel(ID, At) != DiagnosticsEngine::Ignored);
      return On;
    }

    // A system header changed the warnings of the code that includes it. The finding sits at the include that brought it in.
    // An include that is no file, as `-include` makes, has no place of its own. Then the finding sits at the start of the main file.
    void leak(FileID Header) {
      SourceLocation Include = SM.getIncludeLoc(Header);
      if (Include.isInvalid() || !SM.getFileEntryForID(SM.getFileID(Include)))
        Include = SM.getLocForStartOfFile(SM.getMainFileID());
      report(SM.getExpansionLoc(Include), "pragma diagnostic: a system header changes the warnings of the code that includes it. It silences the gate.");
    }

    void FileChanged(SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind Kind, FileID Previous) override {
      const bool System = SrcMgr::isSystem(Kind);
      if (Reason == EnterFile) {
        Frame Entered;
        Entered.System = System;
        // A buffer that is no file, as `<built-in>`, holds no header.
        if (System && !SystemFrames && SM.getFileEntryForID(SM.getFileID(Loc))) {
          Entered.Outermost = true;
          Entered.Enforced = levels(SM.getIncludeLoc(SM.getFileID(Loc)));
        }
        SystemFrames += System;
        Frames.push_back(std::move(Entered));
      } else if (Reason == ExitFile && !Frames.empty()) {
        const Frame Ended = std::move(Frames.back());
        Frames.pop_back();
        SystemFrames -= Ended.System;
        if (!Ended.Outermost || System)
          return;
        // The file resumes. A warning that the header found on and that is off here, the header turned off.
        const std::vector<bool> Now = levels(Loc);
        for (size_t I = 0; I < Now.size() && I < Ended.Enforced.size(); ++I)
          if (Ended.Enforced[I] && !Now[I]) {
            leak(Previous);
            return;
          }
      }
    }

    void PragmaDiagnostic(SourceLocation Loc, StringRef, diag::Severity, StringRef) override { diagnostic(Loc); }
    void PragmaDiagnosticPush(SourceLocation Loc, StringRef) override { diagnostic(Loc); }
    void PragmaDiagnosticPop(SourceLocation Loc, StringRef) override { diagnostic(Loc); }

    void InclusionDirective(SourceLocation HashLoc, const Token &, StringRef FileName, bool, CharSourceRange, OptionalFileEntryRef, StringRef,
                            StringRef, const Module *, SrcMgr::CharacteristicKind) override {
      const SourceLocation At = SM.getExpansionLoc(HashLoc);
      if (FileName.contains('\\') && At.isValid() && !SM.isInSystemHeader(At))
        report(At, "include: a header name with a backslash is not allowed in verified code. The compiler may read it as another file.");
    }

    // Where a pragma starts. A `#pragma` starts at its hash, and its words follow the word `pragma`.
    // A `__pragma` starts at its introducer, and its words follow `__pragma(`. The text of a `_Pragma` starts at its words.
    enum class Start { Hash, Microsoft, Text };

    // The words of the pragma that starts at `Where`, with the place of the first one.
    // The compiler's lexer reads them, in raw mode. So a splice, a comment, a digraph and a trigraph are what the build says.
    // The words are the tokens up to a parenthesis.
    // A fresh raw lexer marks its first token as the start of a line. So it starts at the introducer, and the first token is skipped.
    std::vector<std::string> wordsFrom(SourceLocation Where, Start How, SourceLocation &First) const {
      const SourceLocation Spelling = SM.getSpellingLoc(Where);
      const auto [File, Offset] = SM.getDecomposedLoc(Spelling);
      bool Invalid = false;
      const StringRef Buffer = SM.getBufferData(File, &Invalid);
      if (Invalid || Offset > Buffer.size())
        return {};
      const char *Start = Buffer.data() + Offset, *End = Buffer.end();
      // A scratch buffer holds many strings, and each ends at its own null character.
      if (SM.isWrittenInScratchSpace(Spelling)) {
        const size_t Nul = StringRef(Start, Buffer.end() - Start).find('\0');
        if (Nul != StringRef::npos)
          End = Start + Nul;
      }
      Lexer Raw(SM.getLocForStartOfFile(File), PP.getLangOpts(), Buffer.begin(), Start, End);
      std::string Text;
      Token Tok;
      bool FirstToken = true, InIntroducer = How == Start::Hash;
      unsigned Skip = How == Start::Microsoft ? 2 : 0, Budget = 4;
      for (bool AtEnd = false; !AtEnd;) {
        AtEnd = Raw.LexFromRawLexer(Tok);
        if (Tok.is(tok::eof) || (!FirstToken && Tok.isAtStartOfLine()))
          break;
        FirstToken = false;
        if (InIntroducer) {
          // The hash, then `pragma`. Nothing else may stand between them but what the lexer skips.
          if (Lexer::getSpelling(Tok, SM, PP.getLangOpts()) == "pragma")
            InIntroducer = false;
          else if (!--Budget)
            return {};
          continue;
        }
        if (Skip) {
          --Skip;
          continue;
        }
        if (Tok.isOneOf(tok::l_paren, tok::r_paren))
          break;
        // The last character of the word. A splice before the word belongs to the line that the word ends on.
        if (First.isInvalid())
          First = Tok.getLocation().getLocWithOffset(Tok.getLength() ? Tok.getLength() - 1 : 0);
        Text += Lexer::getSpelling(Tok, SM, PP.getLangOpts()) + " ";
      }
      std::vector<std::string> Words;
      std::string Word;
      for (const char C : Text + " ") {
        if (isalnum(static_cast<unsigned char>(C)) || C == '_') {
          Word += C;
        } else if (!Word.empty()) {
          Words.push_back(std::move(Word));
          Word.clear();
        }
      }
      if (Words.size() > 2)
        Words.resize(2);
      return Words;
    }

    void PragmaDirective(SourceLocation Loc, PragmaIntroducerKind Kind) override {
      DiagnosticSeen = false;
      SourceLocation First;
      std::vector<std::string> Words;
      if (Kind == PIK___pragma)
        Words = wordsFrom(Loc, Start::Microsoft, First);
      else if (Kind == PIK_HashPragma)
        Words = wordsFrom(Loc, Start::Hash, First);
      else if (PreprocessorLexer *Current = PP.getCurrentLexer())
        // The only lexer of the preprocessor is the compiler's `Lexer`. The text of a `_Pragma` has one of its own.
        Words = wordsFrom(static_cast<Lexer *>(Current)->getSourceLocation(), Start::Text, First);
      // A `#pragma` is reported at its first word, and the others where the compiler read them.
      const SourceLocation At = SM.getExpansionLoc(Kind == PIK_HashPragma && First.isValid() ? First : Loc);
      // A `#pragma` reads its name with no macro expansion, so `#pragma once` is the real one. The words of a `__pragma` are expanded first.
      if (At.isInvalid() || SM.isInSystemHeader(At) || (Kind == PIK_HashPragma && !Words.empty() && Words[0] == "once"))
        return;
      std::string Sentence;
      if (Words.size() == 2 && (Words[0] == "clang" || Words[0] == "GCC") && Words[1] == "diagnostic") {
        Sentence = "pragma diagnostic: not allowed in verified code. It silences the gate.";
        DiagnosticSeen = true;
      }
      else if (Words.size() == 2 && Words[1] == "system_header")
        Sentence = "pragma system_header: not allowed in verified code. It silences the gate.";
      else
        Sentence = std::string("pragma") + (Words.empty() ? "" : " " + Words[0] + (Words.size() > 1 ? " " + Words[1] : "")) +
                   ": not allowed in verified code. It changes the build the proofs assume.";
      report(At, Sentence);
    }
  };
};

// ------------------------------------------------------------ markers, decisions 0039 and 0047

// The reason of a marker is its first argument, a string literal with something in it. Empty when it has none.
std::string reasonOf(const AnnotateAttr *Note) {
  if (Note->args_size() == 0)
    return "";
  const auto *Text = dyn_cast<StringLiteral>((*Note->args_begin())->IgnoreImplicit()->IgnoreParens());
  return Text && Text->getCharByteWidth() == 1 ? Text->getString().trim().str() : "";
}

bool hasReason(const AnnotateAttr *Note) { return !reasonOf(Note).empty(); }

// A reason is one line, decision 0103: it holds no byte below 0x20, so it cannot put a line of its own into the report.
bool oneLine(const AnnotateAttr *Note) {
  const std::string Reason = reasonOf(Note);
  return std::none_of(Reason.begin(), Reason.end(), [](unsigned char C) { return C < 0x20; });
}

} // namespace

std::optional<TrustedMark> trustedReason(const FunctionDecl *Function) {
  if (declaredKind(Function) != MarkerKind::Trusted)
    return std::nullopt;
  TrustedMark Mark;
  for (const FunctionDecl *D : declarationsOf(patternOf(Function)))
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      if (markerKind(Note->getAnnotation()) != MarkerKind::Trusted || (Mark.At && !Mark.Reason.empty()))
        return;
      if (!Mark.At || !reasonOf(Note).empty())
        Mark = {reasonOf(Note), D};
    });
  return Mark;
}

namespace {

// The reader of the markers. It walks the tree of one translation unit, outside the system headers, and reports in two forms under the
// name `cplusp-markers`. A third form, `reach {name}`, comes from the table of the lowered form, see `MarkersCheck`. A fourth,
// `uses {name}`, comes from `PlainUses`.
//  1. A region: the body of a function the file writes, or a plain declaration: a plain function, a plain class, a member of a plain
//     class that is written outside it, and the definition of its static data member. The diagnostic sits on the first byte of the region, so
//     the gate has that offset from clang-tidy as it has the offset of every finding. The message is
//     `region {verified|trusted|plain} {end offset}`, with no tab. The end offset is the offset of the byte after the last token. Both
//     offsets are those of the file place of the token. The region is no finding, and the gate keeps it and shows it to no bot.
//     Every function the file writes has one: a function, a member of a local class, an explicit specialization, and a lambda's body.
//     An instantiation and an implicit function have none. The core's `kind_at` picks the innermost region of a place.
//  2. A finding of the gate's own, with the exact words of the test: `{presumed file}\t{presumed line}\t{sentence}`, as the pragma check
//     reports. The sentence starts with `marker: `, and the gate maps it to the rule `marker`.
// A function takes the kind of the markers written on its own declarations. A marker with no reason is still honoured and still
// refused. Two kinds make the function verified. A trusted function has its body for its region, from the first written initializer or
// the brace. A plain function has every declaration, from its first token, which is the marker or the `template`, to its last.
// A trusted or plain function whose first or last token is in a macro is refused and has no region, so its body is verified. A function
// of any kind whose first and last token are in two files is refused and has no region, a lambda too. Code in a plain body is plain:
// a lambda, a local class and its members have no region of their own, and the region of the plain function covers them.
// ponytail: two ceilings. The semicolon after a declaration is not in its region. A plain method of a class template with a base that
// depends on the parameter is checked for its override at no instantiation, because the walk reads the pattern only. A virtual call
// that can run it is a call of the plain method, which the table of the lowered form reports.
// Upgrade: a visit of the instantiations for the override.
class MarkerReader : public RecursiveASTVisitor<MarkerReader> {
public:
  MarkerReader(ClangTidyCheck &Check, ASTContext &Context) : Check(Check), Context(Context), SM(Context.getSourceManager()) {}

  void read() { TraverseAST(Context); }

  bool TraverseDecl(Decl *D) {
    if (D && !isa<TranslationUnitDecl>(D) && isSystem(D->getLocation()))
      return true;
    return RecursiveASTVisitor<MarkerReader>::TraverseDecl(D);
  }

  // A declaration that is no function and no class takes no marker. A class takes a plain marker, decision 0051.
  bool VisitDecl(Decl *D) {
    if (D->isImplicit() || isa<FunctionDecl, FunctionTemplateDecl>(D))
      return true;
    forEachMarker(D, [&](const AnnotateAttr *Note) {
      const MarkerKind Named = markerKind(Note->getAnnotation());
      if (Named == MarkerKind::None)
        reportNoMarker(D, Note);
      else if (const auto *Class = dyn_cast<CXXRecordDecl>(D); Class && Named == MarkerKind::Plain)
        reportNoReason(Class, Note);
      else
        report(D, describe(D) + " has a marker, and only a function or a plain type takes one.");
    });
    return true;
  }

  // A plain class is plain from its first token to its last, with what it holds. A class nested in a plain class or defined in a plain
  // function has the region of that, and so has a member defined in the class. A class defined outside the plain class that holds it
  // gets a region of its own.
  bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    if (!R->isThisDeclarationADefinition() || R->isImplicit() || R->isLambda() || !insidePlain(R) || coveredByPlain(R))
      return true;
    SourceLocation First = R->getBeginLoc();
    if (const ClassTemplateDecl *Template = R->getDescribedClassTemplate())
      First = Template->getBeginLoc();
    else if (const auto *Partial = dyn_cast<ClassTemplatePartialSpecializationDecl>(R))
      First = earlier(First, Partial->getTemplateParameters()->getTemplateLoc());
    SourceLocation Begin = First;
    for (const Attr *A : R->attrs())
      if (!A->isInherited() && !A->isImplicit())
        Begin = earlier(Begin, A->getRange().getBegin());
    place(R, MarkerKind::Plain, {First, R->getEndLoc()}, Begin);
    return true;
  }

  // The definition of a static data member outside its plain class is plain code too, `int Record::made = 0;`.
  bool VisitVarDecl(VarDecl *V) {
    if (V->isStaticDataMember() && V->isThisDeclarationADefinition() && !V->isImplicit() && insidePlain(V) && !coveredByPlain(V))
      place(V, MarkerKind::Plain, {V->getOuterLocStart(), V->getEndLoc()}, V->getOuterLocStart());
    return true;
  }

  bool VisitFunctionDecl(FunctionDecl *F) {
    // The compiler writes an implicit function, and an instantiation has the region of its pattern, which the walk meets too.
    if (F->isImplicit() || F->isTemplateInstantiation())
      return true;
    const MarkerKind Kind = kindOf(F);
    // Code in a plain body is plain, and the region of the plain function or class covers it, decisions 0048 and 0051.
    if (coveredByPlain(F))
      return true;
    // A plain function has a region over every declaration. So has a member of a plain class that is written outside it.
    if (insidePlain(F)) {
      place(F, MarkerKind::Plain, {firstTokenOf(F), F->getEndLoc()}, firstMarkerOf(F));
      return true;
    }
    // A function written in a plain class or function that is not plain itself keeps its declaration in view, decision 0052: a member
    // with a marker of its own, and a friend that the class defines. Its declaration is verified, and a trusted body sits on top of that.
    // A friend declaration has no code of its own, so it stays plain.
    if (insidePlain(outerOf(F, true)) && (F->getFriendObjectKind() == Decl::FOK_None || F->doesThisDeclarationHaveABody()))
      place(F, MarkerKind::Verified, {firstTokenOf(F), F->getEndLoc()}, firstMarkerOf(F));
    if (F->doesThisDeclarationHaveABody()) {
      const SourceRange Body = bodyRange(F);
      place(F, Kind == MarkerKind::Trusted ? Kind : MarkerKind::Verified, Body, Body.getBegin());
    }
    return true;
  }

  // A lambda is a function of its own with no marker, so it is verified inside a verified or a trusted body, and plain inside a plain
  // one. Its body is its region.
  bool VisitLambdaExpr(LambdaExpr *E) {
    const SourceRange Body = E->getBody()->getSourceRange();
    if (insidePlain(E->getLambdaClass()))
      return true;
    if (!keepsEnds(false, Body))
      reportAt(Check, SM, startOf(E->getBeginLoc()), "marker: this lambda " + std::string(EndsInTwoFiles));
    else
      addRegion(Body, MarkerKind::Verified);
    return true;
  }

private:
  ClangTidyCheck &Check;
  ASTContext &Context;
  const SourceManager &SM;
  std::map<const FunctionDecl *, MarkerKind> Kinds;  // by first declaration, so that each function is read and refused once

  bool isSystem(SourceLocation Loc) const { return Loc.isValid() && SM.isInSystemHeader(SM.getExpansionLoc(Loc)); }
  // Where a token starts in its file, and the place after it. A token from a macro stands at the call of the macro.
  SourceLocation startOf(SourceLocation Loc) const { return Loc.isValid() ? SM.getExpansionRange(Loc).getBegin() : Loc; }
  SourceLocation afterEndOf(SourceLocation Loc) const {
    return Loc.isValid() ? Lexer::getLocForEndOfToken(SM.getExpansionRange(Loc).getEnd(), 0, SM, Context.getLangOpts()) : Loc;
  }
  SourceLocation earlier(SourceLocation A, SourceLocation B) const {
    return B.isValid() && (A.isInvalid() || SM.isBeforeInTranslationUnit(B, A)) ? B : A;
  }

  static std::string describe(const Decl *D) {
    const auto *Named = dyn_cast<NamedDecl>(D);
    return Named && !Named->getName().empty() ? Named->getNameAsString() : "this declaration";
  }
  void report(const Decl *At, const std::string &Sentence) { reportAt(Check, SM, startOf(At->getLocation()), "marker: " + Sentence); }
  void reportNoReason(const NamedDecl *At, const AnnotateAttr *Note) {
    if (!hasReason(Note))
      report(At, At->getQualifiedNameAsString() + " has a marker with no reason. A trusted or plain marker gives its reason.");
  }
  void reportNoMarker(const Decl *At, const AnnotateAttr *Note) {
    const std::string Word = Note->getAnnotation().str();
    report(At, Word == "cplusp:assume" ? Word + " waits until a case needs it. Mark the function trusted with a reason."
                                       : Word + " is no marker. The markers are in include/cplusp.h.");
  }

  // The kind of a function. The first read refuses what is wrong with its markers, on every declaration in a user file.
  MarkerKind kindOf(const FunctionDecl *Function) {
    const auto Known = Kinds.find(Function->getFirstDecl());
    if (Known != Kinds.end())
      return Known->second;
    const std::string Name = Function->getQualifiedNameAsString();
    MarkerKind First = MarkerKind::None;
    const FunctionDecl *Brings = nullptr;  // the declaration with the first marker
    bool Twice = false;
    for (const FunctionDecl *D : declarationsOf(Function)) {
      if (isSystem(D->getLocation()))
        continue;
      forEachMarker(D, [&](const AnnotateAttr *Note) {
        const MarkerKind Named = markerKind(Note->getAnnotation());
        if (Named == MarkerKind::None)
          return reportNoMarker(D, Note);
        if (Named != MarkerKind::Verified && !hasReason(Note))
          report(D, Name + " has a marker with no reason. A trusted or plain marker gives its reason.");
        else if (Named != MarkerKind::Verified && !oneLine(Note))
          report(D, Name + " has a reason with a line break. A reason is one line.");
        if (First == MarkerKind::None) {
          First = Named;
          Brings = D;
        } else if (First != Named && !Twice) {
          Twice = true;
          report(D, Name + " has two kinds of marker. A function has one kind.");
        }
      });
    }
    const MarkerKind Kind = declaredKind(Function);
    if (Kind == MarkerKind::Trusted && Brings && !contractOf(SM, Function).Any)
      report(Brings, Name + " is trusted and has no contract. Its callers rest on the contract alone.");
    // A call of the base can run the override. A verified function may call the base, so the override must be as good as the base. A
    // member of a plain class is plain whether or not a marker says it, decision 0052. A marker brings the report to its declaration.
    if (const auto *Method = dyn_cast<CXXMethodDecl>(Function); Method && insidePlain(Function))
      for (const CXXMethodDecl *Base : cast<CXXMethodDecl>(Method->getCanonicalDecl())->overridden_methods())
        if (!insidePlain(Base)) {
          const std::string Over = Base->getQualifiedNameAsString();
          report(Brings ? Brings : Function, Method->getQualifiedNameAsString() + " is plain and overrides " + Over +
                                                  ", which is not plain. A verified call of " + Over + " can run it.");
        }
    return Kinds[Function->getFirstDecl()] = Kind;
  }

  // A body: the written constructor initializers, which the compiler sorts by member, and the block, as written. A macro stays a macro.
  SourceRange bodyRange(const FunctionDecl *F) const {
    const Stmt *Body = F->getBody();
    SourceLocation First = Body->getBeginLoc();
    if (const auto *Constructor = dyn_cast<CXXConstructorDecl>(F))
      for (const CXXCtorInitializer *Init : Constructor->inits())
        if (Init->isWritten())
          First = earlier(First, Init->getSourceRange().getBegin());
    return {First, Body->getEndLoc()};
  }

  static constexpr const char *EndsInTwoFiles =
      "starts or ends in a macro or in another file. Write its first and last token in its own file.";

  // Whether the first and last token of a function, as written, are in one file. A marked function keeps them outside a macro too.
  bool keepsEnds(bool Marked, SourceRange Edges) const {
    const SourceLocation First = Edges.getBegin(), Last = Edges.getEnd();
    if (First.isInvalid() || Last.isInvalid() || (Marked && (First.isMacroID() || Last.isMacroID())))
      return false;
    return SM.isWrittenInSameFile(startOf(First), startOf(Last));
  }

  // Where a function starts, with the markers before it. The marker before the first token is a macro itself.
  SourceLocation firstMarkerOf(const FunctionDecl *F) const {
    SourceLocation Begin = firstTokenOf(F);
    for (const Attr *A : F->attrs())
      if (!A->isInherited() && !A->isImplicit())
        Begin = earlier(Begin, A->getRange().getBegin());
    return Begin;
  }

  // The region of a function. `Edges` are its first and last token as written, and `Begin` is where the region starts, which is earlier
  // than the first token when a marker comes before it. The marker before the first token is a macro itself, and it is no edge. A function
  // that does not keep its ends has no region and is refused, whatever its kind, decisions 0047 and 0048.
  void place(const NamedDecl *F, MarkerKind Kind, SourceRange Edges, SourceLocation Begin) {
    if (!keepsEnds(Kind != MarkerKind::Verified, Edges)) {
      report(F, F->getQualifiedNameAsString() + " " + EndsInTwoFiles);
      return;
    }
    addRegion({Begin, Edges.getEnd()}, Kind);
  }

  void addRegion(SourceRange Range, MarkerKind Kind) {
    const SourceLocation Begin = startOf(Range.getBegin()), After = afterEndOf(Range.getEnd());
    if (Begin.isInvalid() || After.isInvalid() || !SM.isWrittenInSameFile(Begin, After) || SM.getFileOffset(After) <= SM.getFileOffset(Begin))
      return;
    const char *Word = Kind == MarkerKind::Trusted ? "trusted" : Kind == MarkerKind::Plain ? "plain" : "verified";
    Check.diag(Begin, "region %0 %1") << Word << StringRef(std::to_string(SM.getFileOffset(After)));
  }
};

// Whether a declaration is the library's: a system header declares it. A type of the library holds what its type arguments hold, and the
// library reads what it holds. The place decides, as for `inLibrary`, but the namespace does not: `__gnu_cxx` is the library too.
bool inSystemHeader(const Decl *D) {
  const SourceManager &SM = D->getASTContext().getSourceManager();
  return D->getLocation().isInvalid() || SM.isInSystemHeader(SM.getExpansionLoc(D->getLocation()));
}

const CXXRecordDecl *plainHeld(QualType Type);

// The plain class that a type argument of the library holds, or null. A pack holds what its elements hold.
const CXXRecordDecl *plainInArguments(ArrayRef<TemplateArgument> Args) {
  for (const TemplateArgument &A : Args)
    if (const CXXRecordDecl *Class = A.getKind() == TemplateArgument::Type   ? plainHeld(A.getAsType())
                                     : A.getKind() == TemplateArgument::Pack ? plainInArguments(A.pack_elements())
                                                                             : nullptr)
      return Class;
  return nullptr;
}

// The plain class that a value of a type is or holds, or null, decisions 0051 and 0052. An array holds its elements. A reference and a
// pointer hold nothing. A type of the library holds what its type arguments and the type around it hold, as the walk of decision 0046
// goes, so `std::vector<Record>` holds a `Record`. A type of the file that is not plain holds nothing here, because its own fields say.
const CXXRecordDecl *plainHeld(QualType Type) {
  const CXXRecordDecl *Class = Type.isNull() ? nullptr : Type->getBaseElementTypeUnsafe()->getAsCXXRecordDecl();
  if (!Class)
    return nullptr;
  if (insidePlain(Class))
    return Class;
  if (!inSystemHeader(Class))
    return nullptr;
  if (const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(Class))
    if (const CXXRecordDecl *Held = plainInArguments(Spec->getTemplateArgs().asArray()))
      return Held;
  if (const auto *Outer = dyn_cast<CXXRecordDecl>(Class->getDeclContext()))
    return plainHeld(Class->getASTContext().getRecordType(Outer));
  return nullptr;
}

// The class that holds a member, and for a member of an anonymous union the class around it that has a name.
const CXXRecordDecl *plainOwner(const NamedDecl *Member) {
  const auto *Class = dyn_cast<CXXRecordDecl>(Member->getDeclContext());
  while (Class && Class->getDeclName().isEmpty() && isa<CXXRecordDecl>(Class->getDeclContext()))
    Class = cast<CXXRecordDecl>(Class->getDeclContext());
  return Class && insidePlain(Class) ? Class : nullptr;
}

// The uses of a plain type, decisions 0051 to 0054. Verified code makes no object of one: a variable, a field, a temporary, a `new` or a
// base. The same holds for a type of the library that holds one. It reads no field and no static data member of one, also in code that the
// compiler writes, as a structured binding does. It hands a plain object, or a pointer to one, only to a function that the file writes,
// because the library can read or copy what it gets. It casts such a pointer to no other type, because after the cast no callee can be
// judged. A reference and a pointer of the same type are allowed, and so is a call of a member that the file writes, which the reach rule
// judges. The reader reports `uses {class}` at each of these, wherever it is, and the gate keeps the ones in a verified place. A
// template is read at each instantiation too, and the place of an instantiation is the place of its pattern.
// ponytail: one ceiling. A use in an unevaluated operand, as in `sizeof(Record())`, is reported as well. Upgrade: a check of the types and
// the calls that the lowered form makes.
class PlainUses : public RecursiveASTVisitor<PlainUses> {
public:
  PlainUses(ClangTidyCheck &Check, ASTContext &Context) : Check(Check), Context(Context), SM(Context.getSourceManager()) {}

  void read() { TraverseAST(Context); }
  bool shouldVisitTemplateInstantiations() const { return true; }
  bool shouldVisitImplicitCode() const { return true; }

  bool TraverseDecl(Decl *D) {
    if (D && !isa<TranslationUnitDecl>(D) && D->getLocation().isValid() && SM.isInSystemHeader(SM.getExpansionLoc(D->getLocation())))
      return true;
    return RecursiveASTVisitor<PlainUses>::TraverseDecl(D);
  }

  bool VisitVarDecl(VarDecl *V) { return byValue(V->getType(), V->getLocation()); }
  bool VisitFieldDecl(FieldDecl *F) { return byValue(F->getType(), F->getLocation()); }
  bool VisitCXXNewExpr(CXXNewExpr *E) { return byValue(E->getAllocatedType(), E->getBeginLoc()); }
  // A temporary is an expression that is a value of the type. This holds a call that returns the type, a conversion and a copy.
  bool VisitExpr(Expr *E) { return E->isPRValue() ? byValue(E->getType(), E->getBeginLoc()) : true; }
  bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    if (R->hasDefinition() && R->isThisDeclarationADefinition())
      for (const CXXBaseSpecifier &Base : R->bases())
        byValue(Base.getType(), Base.getBaseTypeLoc());
    return true;
  }
  bool VisitMemberExpr(MemberExpr *E) { return member(E->getMemberDecl(), E->getMemberLoc()); }
  bool VisitDeclRefExpr(DeclRefExpr *E) { return member(E->getDecl(), E->getLocation()); }
  // A call, also of a member or an operator, and a construction. The object of a member call is an argument too.
  bool VisitCallExpr(CallExpr *E) {
    if (const auto *Member = dyn_cast<CXXMemberCallExpr>(E))
      given(E->getDirectCallee(), Member->getImplicitObjectArgument());
    for (const Expr *Argument : E->arguments())
      given(E->getDirectCallee(), Argument);
    return true;
  }
  // A cast of a pointer to a plain object into a pointer of another type, written or made by the compiler, decision 0054. A `const void*`
  // keeps no type, so after the cast no callee can be judged on what it gets. A conversion to a base of the class counts too.
  bool VisitCastExpr(CastExpr *E) {
    const QualType From = E->getSubExpr()->getType();
    if (From->isPointerType() && E->getType()->isPointerType())
      if (const CXXRecordDecl *Class = plainPointee(From); Class && !sameClass(Class, plainPointee(E->getType())))
        use(Class, E->getBeginLoc());
    return true;
  }
  bool VisitCXXConstructExpr(CXXConstructExpr *E) {
    for (const Expr *Argument : E->arguments())
      given(E->getConstructor(), Argument);
    return true;
  }

private:
  ClangTidyCheck &Check;
  ASTContext &Context;
  const SourceManager &SM;
  std::set<std::pair<SourceLocation::UIntTy, const CXXRecordDecl *>> Seen;

  bool byValue(QualType Type, SourceLocation At) {
    use(plainHeld(Type), At);
    return true;
  }
  // A field, or a static data member.
  bool member(const ValueDecl *Member, SourceLocation At) {
    if (isa<FieldDecl>(Member) || (isa<VarDecl>(Member) && cast<VarDecl>(Member)->isStaticDataMember()))
      use(plainOwner(Member), At);
    return true;
  }
  // A plain object, by value or by reference, or a pointer to one, goes to a callee that the file does not write, decision 0053. A callee
  // with no name, as a pointer to a function is, may be the library's, so it counts. A function the file writes is judged by its own
  // kind, and the reach rule judges the call. A pointer counts as its object, because a C call such as `std::fwrite` takes an object so.
  // A pointer that is cast to another type is a use at the cast, `VisitCastExpr`.
  void given(const FunctionDecl *Callee, const Expr *Argument) {
    if (!Argument || (Callee && !inSystemHeader(Callee)))
      return;
    const CXXRecordDecl *Class = plainPointee(Argument->getType());
    use(Class ? Class : plainPointee(Argument->IgnoreParenImpCasts()->getType()), Argument->getBeginLoc());
  }
  static bool sameClass(const CXXRecordDecl *A, const CXXRecordDecl *B) { return B && A->getCanonicalDecl() == B->getCanonicalDecl(); }
  static const CXXRecordDecl *plainPointee(QualType Type) {
    while (!Type.isNull() && Type->isPointerType())
      Type = Type->getPointeeType();
    return plainHeld(Type);
  }
  void use(const CXXRecordDecl *Class, SourceLocation At) {
    if (!Class || At.isInvalid() || SM.isInSystemHeader(SM.getExpansionLoc(At)))
      return;
    At = SM.getExpansionLoc(At);
    if (Seen.insert({At.getRawEncoding(), Class->getCanonicalDecl()}).second)
      Check.diag(At, "uses %0") << StringRef(Class->getQualifiedNameAsString());
  }
};

// cplusp-markers: decisions 0039 and 0047. The plugin reads the markers of include/cplusp.h. See `MarkerReader` for what it reports.
// It reports the calls that run plain code too, from the table of the lowered form, as `reach {qualified name}` at the call. The name
// runs to the end of the message and may hold a space. The gate keeps such a report when the place of the call is verified. Every
// function that the file wrote reports its calls, whatever its kind, because the kind of the place is the gate's to ask.
// A file that the compiler cannot generate code for is refused, because the gate then cannot read what runs.
class MarkersCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    Context = Result.Context;
    MarkerReader(*this, *Result.Context).read();
    PlainUses(*this, *Result.Context).read();
  }
  void onEndOfTranslationUnit() override {
    Lowered &T = table();
    if (!Context)
      return;
    if (!T.generated()) {
      const SourceManager &SM = Context->getSourceManager();
      reportAt(*this, SM, SM.getLocForStartOfFile(SM.getMainFileID()),
               "marker: the compiler could not generate code for this file, so the gate cannot read what runs.");
    }
    for (const Lowered::PlainCall &Call : T.plainCalls())
      diag(Call.Loc, "reach %0") << StringRef(Call.Name);
  }

private:
  ASTContext *Context = nullptr;
};

// cplusp-indirect-call: decision 0048. The row `function_pointers` judges a call too, not only the spelling of a type. Verified code can
// run an indirect call, itself or through code that the file does not write, and a deduced type carries a pointer out of a trusted body
// with none spelled. When the lowered form cannot name each target, the call is a finding of the row, at its line. The gate writes the
// message of the row, so the text here only has to map. The row is trusted only, so the core drops the finding in a trusted or plain place.
class IndirectCallCheck : public ClangTidyCheck {
public:
  using ClangTidyCheck::ClangTidyCheck;
  void onStartOfTranslationUnit() override { startTable(); }
  void registerMatchers(MatchFinder *Finder) override {
    registerTableMatchers(Finder, this);
    Finder->addMatcher(translationUnitDecl(), this);
  }
  void check(const MatchFinder::MatchResult &Result) override {
    giveTable(Result.Context);
    if (collectForTable(Result))
      return;
    Seen = true;
  }
  void onEndOfTranslationUnit() override {
    if (!Seen)
      return;
    for (const SourceLocation &At : table().indirectCalls())
      diag(At, "an indirect call that the gate cannot name the target of");
  }

private:
  bool Seen = false;
};

} // namespace

void addStateChecks(ClangTidyCheckFactories &Factories) {
    Factories.registerCheck<UnlistedStateCheck>("cplusp-unlisted-state");
    Factories.registerCheck<LineDirectiveCheck>("cplusp-line-directive");
    Factories.registerCheck<PragmaCheck>("cplusp-pragma");
    Factories.registerCheck<MarkersCheck>("cplusp-markers");
    Factories.registerCheck<IndirectCallCheck>("cplusp-indirect-call");
}

} // namespace cplusp::detail
