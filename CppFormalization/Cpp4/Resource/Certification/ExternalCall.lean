import CppFormalization.Cpp4.Resource.Certification.Noninterference
import CppFormalization.Cpp4.Resource.Noninterference.Call

/-!
# CppFormalization.Cpp4.Resource.Certification.ExternalCall

Certification bridge for the minimal external-call contract.

This file does not introduce user-facing contracts.  It only turns the
resource-level external-call contract into the same `NoninterferenceCertificate`
used by the rest of the certification pipeline.
-/

namespace Cpp4

namespace ExternalCallPreservesContract

/-- Turn the minimal external-call contract into the certification pipeline's
noninterference certificate for the `.callExternal f` effect. -/
def toNoninterferenceCertificate
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    NoninterferenceCertificate χ χ' σ σ' [.callExternal f] D D' where
  preserves := h.toPreservesDemandSet

end ExternalCallPreservesContract

/-- Generate the certification-level noninterference certificate required for an
external call from its minimal resource contract. -/
def externalCall_noninterference_of_contract
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    NoninterferenceCertificate χ χ' σ σ' [.callExternal f] D D' :=
  h.toNoninterferenceCertificate

/-- Generate the raw provider for an external call through the certification path.

This is the same preservation theorem as `callExternal_preserves_by_contract`,
but it factors through `NoninterferenceCertificate`, so it fits the pipeline:
external-call contract -> noninterference certificate -> raw provider. -/
def externalCall_provider_of_contract
    {f : FunctionName}
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : ExternalCallPreservesContract f χ χ' σ σ' D D') :
    EffectPreservesDemand χ χ' σ σ' [.callExternal f] D D' :=
  (externalCall_noninterference_of_contract h).toEffectPreservesDemand

end Cpp4
