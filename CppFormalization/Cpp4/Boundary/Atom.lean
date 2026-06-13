import CppFormalization.Cpp4.Boundary.Call
import CppFormalization.Cpp4.Typing.Judgment.Plan.Atom

/-!
# CppFormalization.Cpp4.Boundary.Atom

Runtime boundaries for typed ControlPlan atoms.
-/

namespace Cpp4

/-- A typed primitive atom is enterable when its atom demand is satisfied. -/
structure AtomBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {a : ControlAtom} (h : PlanAtomTyping Γ κ a) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace AtomBoundary

/-- Repackage an atom boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {a : ControlAtom} {h : PlanAtomTyping Γ κ a} (b : AtomBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build an atom boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {a : ControlAtom} {h : PlanAtomTyping Γ κ a}
    (b : DemandBoundary χ σ h.demand.demands) : AtomBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the atom typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {a : ControlAtom} {h : PlanAtomTyping Γ κ a} (_b : AtomBoundary χ σ h) :
    h.formation :=
  h.evidence

end AtomBoundary

end Cpp4
