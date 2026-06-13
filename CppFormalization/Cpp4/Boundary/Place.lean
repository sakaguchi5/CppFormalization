import CppFormalization.Cpp4.Boundary.Core
import CppFormalization.Cpp4.Typing.Micro.Place

/-!
# CppFormalization.Cpp4.Boundary.Place

Runtime boundaries for typed place expressions.
-/

namespace Cpp4

/-- A typed place is enterable in a runtime state when its generated place demand is satisfied. -/
structure PlaceBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {p : PlaceExpr}
    (h : PlaceTyping Γ p) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace PlaceBoundary

/-- Repackage a place boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {p : PlaceExpr}
    {h : PlaceTyping Γ p} (b : PlaceBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a place boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {p : PlaceExpr}
    {h : PlaceTyping Γ p} (b : DemandBoundary χ σ h.demand.demands) :
    PlaceBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the place typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {p : PlaceExpr}
    {h : PlaceTyping Γ p} (_b : PlaceBoundary χ σ h) : h.formation :=
  h.evidence

end PlaceBoundary

end Cpp4
