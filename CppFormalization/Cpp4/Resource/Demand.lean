import CppFormalization.Cpp4.Core.Control
import CppFormalization.Cpp4.Resource.Capability

/-!
# CppFormalization.Cpp4.Resource.Demand

Resource demands: what the next expression/statement/block/call needs from the
current runtime state to avoid unclassified stuckness.
-/

namespace Cpp4

/-- Ambient demand context: control permissions and callable environment. -/
structure DemandContext where
  control : ControlContext
  functions : FunctionEnv

/-- Primitive resource demands. -/
inductive ResourceDemand where
  | nameBound : Ident → ResourceDemand
  | liveObject : Address → ResourceDemand
  | canRead : Address → CppType → ResourceDemand
  | canWrite : Address → CppType → ResourceDemand
  | canDerefRead : PtrValue → CppType → ResourceDemand
  | canDerefWrite : PtrValue → CppType → ResourceDemand
  | activeScope : ScopeId → ResourceDemand
  | topScope : ScopeId → ResourceDemand
  | callable : FunctionName → ResourceDemand
  | breakAllowed
  | continueAllowed
  | returnAllowed : CppType → ResourceDemand

/-- Satisfaction of a primitive resource demand. -/
def DemandSatisfied (χ : DemandContext) (σ : State) : ResourceDemand → Prop
  | .nameBound x => ∃ b, lookupBinding σ x = some b
  | .liveObject a => LiveObject σ a
  | .canRead a τ => CanRead σ a τ
  | .canWrite a τ => CanWrite σ a τ
  | .canDerefRead p τ => CanDerefRead σ p τ
  | .canDerefWrite p τ => CanDerefWrite σ p τ
  | .activeScope sid => ActiveScope σ sid
  | .topScope sid => TopScope σ sid
  | .callable f => CallableResolved χ.functions f
  | .breakAllowed => BreakAllowed χ.control
  | .continueAllowed => ContinueAllowed χ.control
  | .returnAllowed τ => ReturnAllowed χ.control τ

/-- A demand set is a finite list of primitive resource demands. -/
abbrev DemandSet := List ResourceDemand

/-- All demands in a demand set are satisfied. -/
def DemandSetSatisfied (χ : DemandContext) (σ : State) (D : DemandSet) : Prop :=
  ∀ d, d ∈ D → DemandSatisfied χ σ d

/-- Placeholder surface for expression demands.  Later files should compute a real
set from syntax and typing; the Resource layer only fixes the target shape. -/
structure ExprDemand where
  demands : DemandSet

/-- Placeholder surface for statement demands. -/
structure StmtDemand where
  demands : DemandSet

/-- Placeholder surface for block demands. -/
structure BlockDemand where
  demands : DemandSet

/-- Placeholder surface for call demands. -/
structure CallDemand where
  demands : DemandSet

end Cpp4
