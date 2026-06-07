namespace Cpp3
namespace Contracts

/-!
# CppFormalization.Cpp3.Contracts.Core.Kind

Classification labels for Cpp3 explicit evidence.

This file intentionally contains only names and roles.  It does not provide any
program obligation globally, and it does not prove any safety theorem.

The split is:

* `CertifiedFamily`:
  facts that should be derived from lower layers, such as typing components,
  semantic routing rules, boundary definitions, or stability theorems.

* `ObligationFamily`:
  programmer-facing C++ correctness obligations.  These describe practical
  safety promises such as "this pointer does not dangle", "this write does not
  invalidate the later read", or "this loop body preserves the next guard
  evaluation".

The important design rule is that C++ control-flow semantics itself is not a
programmer obligation.  For example, "if selects one branch" and "while returns
to the condition after normal/continue" belong to Semantics/Certified facts.
The obligations here are only about whether the post-state still satisfies the
boundary needed by the next program point.
-/

/-- Families of facts that should be theorem-backed or obtained from lower
certificates.

These are not programmer-facing restrictions.  They are facts that the
formalization should derive from Core/Typing/Semantics/Boundary/Stability layers.
-/
inductive CertifiedFamily where
  /- Primitive/static micro facts. -/
  | primitiveFormation
  | primitiveControlEffect
  | primitiveEnvEffect
  | expressionStatementFormation
  | assignmentFormation
  | declarationFormation
  | initializerStatic
  | conditionStatic
  | jumpFormation

  /- Compound static composition facts. -/
  | normalBindStatic
  | abruptShortCircuitStatic
  | blockConsStatic
  | branchMergeStatic
  | whileChannelsStatic
  | scopeBoundaryStatic

  /- Public judgment reconstruction/inversion facts. -/
  | typingReconstruction
  | typingInversion

  /- Semantic routing facts: these are C++ semantics, not contracts. -/
  | semanticRouting
  | selectedBranchRouting
  | whileBackedgeRouting
  | blockOpenBodyCloseRouting
  | jumpControlRouting

  /- Boundary/Stability/Soundness theorem-backed facts. -/
  | boundaryDerived
  | stabilityDerived
  | statePreservation
  | soundnessDerived
  deriving DecidableEq, Repr

/-- Families of programmer-facing C++ correctness obligations.

These are the meaningful contracts that remain after C++ syntax, typing, and
control-flow routing have been separated.

They should be understandable as practical C++ safety promises:
* do not create dangling pointers/references;
* only dereference live/readable/writable targets;
* do not let a write invalidate a later read/condition;
* preserve a loop guard across the body;
* specify what external calls read/write/return.
-/
inductive ObligationFamily where
  /- Lifetime / scope safety. -/
  | noInnerAddressEscape
  | lifetimeOutlivesUse
  | closeScopeNoDanglingOuterPointer
  | scopeDoesNotLeakInvalidReference

  /- Dereference / read / write safety. -/
  | derefTargetLive
  | readableTargetAvailable
  | writableTargetAvailable
  | typedStorageAvailable

  /- Footprint / non-interference safety. -/
  | readFootprintPreserved
  | writeFootprintSeparated
  | readWriteFootprintSeparated
  | aliasSeparated

  /- Post-state boundary preservation. -/
  | tailBoundaryPreserved
  | conditionBoundaryPreserved
  | branchBoundaryAfterCondition
  | openedBlockBodyBoundaryPreserved

  /- Loop safety, without requiring termination. -/
  | loopGuardPreservedByBody
  | loopBodyPreservesBackedgeBoundary
  | conditionReplayStable

  /- Assignment/declaration/initializer specific obligations. -/
  | assignmentDoesNotInvalidateLaterUse
  | declarationDoesNotInvalidateLaterUse
  | initializerDoesNotInvalidateDeclarationBoundary

  /- External or not-yet-internalized C++ behavior. -/
  | externalCallSpec
  | externalCallFootprintRespected
  | externalCallLifetimeRespected
  deriving DecidableEq, Repr

/-- A contract label is either certified evidence or a programmer-facing
obligation.

`ContractKind` is only a label.  It does not make any obligation globally
available.
-/
inductive ContractKind where
  | certified : CertifiedFamily → ContractKind
  | obligation : ObligationFamily → ContractKind
  deriving DecidableEq, Repr

end Contracts
end Cpp3
