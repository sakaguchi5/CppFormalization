import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Internal.WhileTailAdequacyProviderSplitCI
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCI

`body_closure_ci_function_body_progress_or_diverges_by_cases` の
constructor-level case-driver body.

重要:
- ここでは closed theorem は作らない。
- while は同じ syntax `(.whileStmt c body)` への tail 再帰を持つので、
  case-driver 本体は明示的な recursive hypothesis を引数に取る。
- `while` branch uses the condition-first post-adequacy-split route.
  It avoids the older unconditional loop-body return exposure compatibility
  shell, the direct tail-boundary-kit extraction shell, the wrapper that hides
  `whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI`, the provider
  wrapper that hides delimiter reentry plus tail adequacy, and now also exposes
  the two post-state tail adequacy channels: normal and continue.
-/

/-- canonical result shape, re-exported for readability at the driver level. -/
abbrev FunctionBodyCaseDriverResult (σ : State) (st : CppStmt) : Prop :=
  FunctionBodyClosureResult σ st

/-- recursive hypothesis consumed by the constructor-level case-driver body. -/
abbrev FunctionBodyCaseDriverIH : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    FunctionBodyCaseDriverResult σ st


end Cpp
