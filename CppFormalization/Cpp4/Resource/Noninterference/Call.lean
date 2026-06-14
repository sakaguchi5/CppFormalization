import CppFormalization.Cpp4.Resource.Noninterference.DemandSet

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Call

Minimal resource-level contracts for external calls.

External calls are the only resource effects in this layer whose preservation
power cannot be derived from the internal C++ operational rules alone.  The
minimal machine contract is therefore stated directly as preservation of the
caller-side future demand set across the `.callExternal f` effect.

This remains below the future user-facing `Contracts` layer: later, richer C++
contracts can imply this minimal resource contract.
-/

namespace Cpp4

/-- Minimal resource-preservation contract for an external call.

C++ reading: calling an external function `f` may change the state from `σ` to
`σ'` and the demand context from `χ` to `χ'`, but it must preserve the future
resource demands promised to the caller. -/
structure ExternalCallPreservesContract
    (f : FunctionName)
    (χ χ' : DemandContext) (σ σ' : State)
    (D D' : DemandSet) : Type where
  preserves : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ' D'

namespace ExternalCallPreservesContract

/-- View the external-call contract as list-level demand preservation.

This is the resource-facing form used by the certification pipeline. -/
def toPreservesDemandSet
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    PreservesDemandSet χ χ' σ σ' [.callExternal f] D D' where
  preserved := h.preserves

/-- View the external-call contract as the raw provider expected by the lower
transport theorem.

This is a derived view, not an additional assumption. -/
def toEffectPreservesDemand
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    EffectPreservesDemand χ χ' σ σ' [.callExternal f] D D' where
  preserved := h.preserves

end ExternalCallPreservesContract

/-- Compatibility name for the existing external-call noninterference surface. -/
def callExternal_preserves_by_contract
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    EffectPreservesDemand χ χ' σ σ' [.callExternal f] D D' :=
  h.toEffectPreservesDemand

end Cpp4
