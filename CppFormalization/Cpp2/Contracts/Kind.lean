namespace Cpp
namespace Contracts

inductive CertifiedFamily where
  | effectDerived
  | freshnessIntro
  | readinessTransport
  | statePreservation
  deriving DecidableEq, Repr

inductive ObligationFamily where
  | replayStable
  | aliasSeparated
  | loopReentry
  | conditionReplay
  | bodyReplay
  | whileBackedge
  | externalAdequacy
  deriving DecidableEq, Repr

inductive ContractKind where
  | certified : CertifiedFamily → ContractKind
  | obligation : ObligationFamily → ContractKind
  deriving DecidableEq, Repr

end Contracts
end Cpp
