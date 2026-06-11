import CppFormalization.Cpp4.Resource.Noninterference.Binding

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Call

External-call noninterference.  The call itself is an atom; its preservation power
comes from an explicit external contract.
-/

namespace Cpp4

/-- Resource-preservation contract for an external call. -/
structure ExternalCallPreservesContract
    (f : FunctionName)
    (χ χ' : DemandContext) (σ σ' : State)
    (D D' : DemandSet) : Type where
  preserves : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ' D'

/-- An external call preserves future demands exactly by its contract. -/
def callExternal_preserves_by_contract
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    EffectPreservesDemand χ χ' σ σ' [.callExternal f] D D' := by
  constructor
  exact h.preserves

end Cpp4
