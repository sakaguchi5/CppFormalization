import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.LoopBodyFunctionClosureCI

`while` body を top-level function body と混同しないための local closure shell.

重要:
- loop body は `break` / `continue` を合法な local exit として持つ。
- したがって top-level `BodyClosureBoundaryCI` の progress theorem ではなく、
  `LoopBodyBoundaryCI` 専用の local theorem surface を別に持つ。
- このファイルではまだ theorem-backed kernel を置かず、
  honest な shell だけを切り出す。
-/

/--
Local progress/divergence shell for a single loop body.

ここでの `ctrl` は raw statement control をそのまま残す。
`while` delimiter 側が `break` を吸収し、`return` を top-level へ通す。
-/
axiom loop_body_function_progress_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {body : CppStmt} :
    LoopBodyBoundaryCI Γ σ body →
    (∃ ctrl σ', BigStepStmt σ body ctrl σ') ∨ BigStepStmtDiv σ body

end Cpp
