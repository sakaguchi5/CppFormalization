import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Core.Syntax
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCI

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
- したがって、残る本丸は constructor case split 自体ではなく、
  same-syntax while tail に対して case-driver body を一貫して回してよいという
  global recursion principle だけである。
- このファイルには、その最小の global recursion shell だけを置く。
-/


/-- A global recursive hypothesis that is intended to close the constructor-level driver body. -/
axiom body_closure_ci_function_body_global_recursion :
    FunctionBodyCaseDriverIH

end Cpp
