#pragma once

#include "ClangTidyCheck.h"
#include "ClangTidyModule.h"
#include "ClangTidyModuleRegistry.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/Dynamic/Diagnostics.h"
#include "clang/ASTMatchers/Dynamic/Parser.h"
#include "clang/AST/ASTLambda.h"
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/CodeGenOptions.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/SourceManagerInternals.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Lex/HeaderSearchOptions.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "clang/Lex/Lexer.h"
#include "clang/Serialization/ASTReader.h"
#include "clang/Serialization/ModuleManager.h"

#include <cmath>
#include <algorithm>
#include <initializer_list>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

using namespace clang;
using namespace clang::ast_matchers;
using clang::tidy::ClangTidyCheck;
using clang::tidy::ClangTidyCheckFactories;
using clang::tidy::ClangTidyContext;
using clang::tidy::ClangTidyModule;

namespace cplusp::detail {

// What more than one file of the plugin needs. Each file adds its checks to the module in its add...Checks function.
void addSyntaxChecks(ClangTidyCheckFactories &Factories);
void addRawCopyChecks(ClangTidyCheckFactories &Factories);
void addStateChecks(ClangTidyCheckFactories &Factories);
void addTreeCheck(ClangTidyCheckFactories &Factories);

bool inStdNamespace(const Decl *Declaration);
bool isMutableType(QualType Type);
bool isMutableGlobal(const VarDecl *Var);
bool notJudgedFunction(const FunctionDecl &Node);
bool insidePlain(const Decl *D);

namespace matchers {
AST_MATCHER(FunctionDecl, notJudged) { return notJudgedFunction(Node); }
}
using matchers::notJudged;

// The table of the lowered form, decision 0037, which the state check reads too. Defined with it.
// A call of `Callee` changes a global when its lines list one or its code in the table writes one or holds a refusal.
// It also changes a global when it has no body and no lines.
bool tableChanges(const FunctionDecl *Callee);
void startTable();
void giveTable(ASTContext *Context);
// The matchers that feed the table, which whichever check is on registers, and the one place that reads their matches.
void registerTableMatchers(MatchFinder *Finder, MatchFinder::MatchCallback *Callback);
bool collectForTable(const MatchFinder::MatchResult &Result);

// The two kinds of contract line the gate reads: `//@ modifies a, b` and `//@ reads a, b`. Every other line is ignored, but it shows
// that the function has a contract, and a contract with no `modifies` line says that the function changes no global.
struct Contract {
  std::vector<std::string> Modifies, Reads;
  // The names of the reference parameters of the function that it may write, in all its declarations: a parameter of type `T&` with no const.
  // A name on a modifies or reads line that is one of them is the parameter, not a global, decision 0111. A parameter by value is no
  // name for a modifies line, so a global of the same name stays the global.
  std::vector<std::string> Parameters;
  bool Any = false;  // a `//@` line of any kind is there
  // Every `//@` line in source order: its file, its line number and its text after the `//@`. The translator, cplusp-tree, reads these.
  // A line that a backslash spliced to the next one is here too, with the backslash at the end of its text. It is no `modifies` or `reads`.
  struct Line {
    unsigned File;  // the hash of the FileID
    unsigned Number;
    std::string Text;
    std::vector<std::string> Params;  // the parameter names of the declaration that the line stands on, "" for an unnamed one
    FileID Id;                        // the file of the line, for its name
  };
  std::vector<Line> Lines;
};
Contract contractAbove(const SourceManager &SM, SourceLocation First, SourceLocation Floor, bool SkipComments);
Contract contractOf(const SourceManager &SM, const FunctionDecl *Function);

// The trusted marker of a function, decisions 0102 and 0103: its reason, and the declaration that wrote it. Nothing when the function is
// not trusted. The reason is empty when the marker has none that can be read, which the markers check refuses.
struct TrustedMark {
  std::string Reason;
  const FunctionDecl *At = nullptr;
};
std::optional<TrustedMark> trustedReason(const FunctionDecl *Function);

} // namespace cplusp::detail
