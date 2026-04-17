import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Core.Syntax
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.CurrentShellCI

Current live high-level CI shell axioms.

役割:
- current mainline でまだ残っている CI-level shell axiom だけを一箇所へ集約する。
- theorem-backed kernel / replay kernel と混ざらないようにする。
- dead / legacy / shell を切り分けたあとに残る「本当にまだ痛い肩代わり」だけを可視化する。

更新:
- generic な `while_function_body_closure_ci` shell はここから外した。
  while の責務は
  `LoopBodyFunctionClosureCI` の local shell と
  `WhileFunctionClosureKernelCI` の honest kernel surface へ分解した。
- seq / ite の constructor shell は `FunctionBodyCaseSplitCI` へ切り出した。
- block の constructor shell は `BlockBodyClosureCI` へ切り出した。
- `BodyReadyCI` 版 master shell も外した。
  canonical surface は `BodyClosureBoundaryCI` なので、
  `BodyReadyCI` entry theorem は closure-boundary theorem から導く。
- このファイルには、最後に残る canonical master case-driver shell だけを置く。
-/

axiom body_closure_ci_function_body_progress_or_diverges_by_cases
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

end Cpp
