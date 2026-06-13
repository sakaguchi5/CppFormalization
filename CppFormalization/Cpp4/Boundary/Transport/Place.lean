import CppFormalization.Cpp4.Boundary.Transport.Core
import CppFormalization.Cpp4.Boundary.Place

/-!
# CppFormalization.Cpp4.Boundary.Transport.Place

Transport for runtime boundaries of typed place expressions.
-/

namespace Cpp4

/-- Transport from one typed-place boundary to another. -/
structure PlaceBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {p p' : PlaceExpr}
    (before : PlaceTyping Γ p) (after : PlaceTyping Γ' p') : Type where
  preserves :
    EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands

namespace PlaceBoundaryTransport

/-- Apply place-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {p p' : PlaceExpr}
    {before : PlaceTyping Γ p} {after : PlaceTyping Γ' p'}
    (b : PlaceBoundary χ σ before)
    (t : PlaceBoundaryTransport χ χ' σ σ' eff before after) :
    PlaceBoundary χ' σ' after where
  demandsSatisfied := demand_transport b.demandsSatisfied t.preserves

/-- View a place-boundary transport as raw demand-boundary transport. -/
def toDemandTransport
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {p p' : PlaceExpr}
    {before : PlaceTyping Γ p} {after : PlaceTyping Γ' p'}
    (t : PlaceBoundaryTransport χ χ' σ σ' eff before after) :
    BoundaryTransport χ χ' σ σ' eff before.demand.demands after.demand.demands where
  preserves := t.preserves

end PlaceBoundaryTransport

end Cpp4
