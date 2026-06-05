namespace Cpp3
namespace Contracts

/-!
# CppFormalization.Cpp3.Contracts.Core.Kind

Classification labels for Cpp3 contracts.

These labels are intentionally lightweight.  They are used to document whether a
piece of evidence is a certified fact derived from the lower microkernel, or a
program-facing obligation supplied by the user/program proof.
-/

/-- Families of facts that should ultimately be theorem-backed or obtained from
lower certificates. -/
inductive CertifiedFamily where
  | primitiveFormation
  | primitiveControlEffect
  | primitiveEnvEffect
  | normalBindStatic
  | abruptShortCircuitStatic
  | blockConsStatic
  | typingReconstruction
  | effectDerived
  | statePreservation
  deriving DecidableEq, Repr

/-- Families of programmer-facing obligations.

These are not proof-architecture shells.  They mark places where C++ effects may
invalidate later program points unless the programmer supplies a meaningful
correctness condition. -/
inductive ObligationFamily where
  | normalBindContinuation
  | blockConsContinuation
  | scopeBoundaryContinuation
  | branchMergeContinuation
  | whileBackedgeInvariant
  | tailStability
  | assignStability
  | derefStability
  | declarationStability
  | replayStable
  | aliasSeparated
  deriving DecidableEq, Repr

/-- A contract label is either certified evidence or a program obligation. -/
inductive ContractKind where
  | certified : CertifiedFamily → ContractKind
  | obligation : ObligationFamily → ContractKind
  deriving DecidableEq, Repr

end Contracts
end Cpp3
