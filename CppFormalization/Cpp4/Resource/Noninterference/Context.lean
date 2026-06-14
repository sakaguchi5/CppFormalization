import CppFormalization.Cpp4.Resource.Noninterference.EffectList

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Context

C1 vocabulary for demand-context changes.

Some demands are state-based, while others mention `DemandContext` directly:
callability and control permissions.  This file isolates preservation caused by a
context transition before it is combined with ordinary resource effects.
-/

namespace Cpp4

/-- Preservation caused by a demand-context change while the state is fixed. -/
structure ContextPreservesDemandSet
    (χ χ' : DemandContext) (σ : State) (D D' : DemandSet) : Type where
  preserved : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ D'

namespace ContextPreservesDemandSet

/-- View a context-only preservation proof as ordinary demand-set preservation
indexed by an arbitrary resource-effect list. -/
def toPreservesDemandSet
    {χ χ' : DemandContext} {σ : State} {D D' : DemandSet}
    (h : ContextPreservesDemandSet χ χ' σ D D')
    (eff : ResourceEffect) :
    PreservesDemandSet χ χ' σ σ eff D D' where
  preserved := h.preserved

/-- Identity context preservation. -/
def refl (χ : DemandContext) (σ : State) (D : DemandSet) :
    ContextPreservesDemandSet χ χ σ D D where
  preserved := id

end ContextPreservesDemandSet

end Cpp4
