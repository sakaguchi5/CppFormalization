import CppFormalization.Cpp4.Boundary.Program
import CppFormalization.Cpp4.Resource.Transport.Core
import CppFormalization.Cpp4.Semantics.Effect.Plan

/-!
# CppFormalization.Cpp4.Boundary.Transport.Core

Boundary transport derived from resource-demand transport.

This layer does not redefine resource effects.  It packages the common pattern
used by later ControlPlan transport components: a finite kernel step exposes a
resource-effect trace, and that effect preserves the demand set needed by the
post-state boundary.
-/

namespace Cpp4

/-- Generic transport between two raw demand boundaries. -/
structure BoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : DemandSet) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before after

namespace BoundaryTransport

/-- Build generic boundary transport from a resource preservation certificate. -/
def ofPreserves
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {before after : DemandSet}
    (h : EffectPreservesDemand χ χ' σ σ' eff before after) :
    BoundaryTransport χ χ' σ σ' eff before after where
  preserves := h

/-- Apply generic boundary transport to a generic demand boundary. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {before after : DemandSet}
    (b : DemandBoundary χ σ before)
    (t : BoundaryTransport χ χ' σ σ' eff before after) :
    DemandBoundary χ' σ' after where
  satisfied := demand_transport b.satisfied t.preserves

/-- Identity transport for unchanged state/context and unchanged demand. -/
def refl {χ : DemandContext} {σ : State} {D : DemandSet} :
    BoundaryTransport χ χ σ σ [] D D where
  preserves := demand_transport_refl

end BoundaryTransport

/-- Boundary transport tied to an explicit semantic effect trace. -/
structure BoundaryStepTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (trace : EffectTrace σ σ') (before after : DemandSet) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' trace.effect before after

namespace BoundaryStepTransport

/-- Forget the semantic trace parameter into ordinary boundary transport. -/
def toBoundaryTransport
    {χ χ' : DemandContext} {σ σ' : State} {trace : EffectTrace σ σ'}
    {before after : DemandSet}
    (t : BoundaryStepTransport χ χ' σ σ' trace before after) :
    BoundaryTransport χ χ' σ σ' trace.effect before after where
  preserves := t.preserves

/-- Apply a trace-indexed boundary transport certificate. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {trace : EffectTrace σ σ'}
    {before after : DemandSet}
    (b : DemandBoundary χ σ before)
    (t : BoundaryStepTransport χ χ' σ σ' trace before after) :
    DemandBoundary χ' σ' after :=
  BoundaryTransport.apply b t.toBoundaryTransport

end BoundaryStepTransport

end Cpp4
