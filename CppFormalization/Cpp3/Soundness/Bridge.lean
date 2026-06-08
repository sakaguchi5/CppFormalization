import CppFormalization.Cpp3.Soundness.NoUnclassifiedStuck
import CppFormalization.Cpp3.Continuation.Registry

/-!
# CppFormalization.Cpp3.Soundness.Bridge

Thin bridges from continuation registries to the closed internal C++ fragment
soundness target.

This file intentionally does not prove structural progress/preservation.  It
only prevents the continuation handoff proposition from staying an arbitrary
`Prop`: for the closed final theorem, the handoff must be read as the semantic
classification target.
-/

namespace Cpp3
namespace Soundness

/-- Statement registry proposition specialized to the closed-fragment target. -/
def StmtReadyForClosedSoundness
    (_Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  ClosedStmtSoundness σ st

/-- Block registry proposition specialized to the closed-fragment target. -/
def BlockReadyForClosedSoundness
    (_Γ : TypeEnv) (σ : State) (body : StmtBlock) : Prop :=
  ClosedBlockSoundness σ body

/-- Function-body registry proposition specialized to the closed-fragment target. -/
def FunctionBodyReadyForClosedSoundness
    (_Γ : TypeEnv) (σ : State) (body : CppStmt) : Prop :=
  ClosedFunctionBodySoundness σ body

/-- A statement continuation registry whose handoff proposition is the closed target. -/
structure ClosedStmtContinuationRegistry
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  registry : Continuation.StmtContinuationRegistry Γ σ st
  ready_eq_closed :
    registry.readyForSoundness = StmtReadyForClosedSoundness Γ σ st

/-- A block continuation registry whose handoff proposition is the closed target. -/
structure ClosedBlockContinuationRegistry
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  registry : Continuation.BlockContinuationRegistry Γ σ body
  ready_eq_closed :
    registry.readyForSoundness = BlockReadyForClosedSoundness Γ σ body

/-- A function-body continuation registry whose handoff proposition is the closed target. -/
structure ClosedFunctionBodyContinuationRegistry
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  registry : Continuation.FunctionBodyContinuationRegistry Γ σ body
  ready_eq_closed :
    registry.readyForSoundness = FunctionBodyReadyForClosedSoundness Γ σ body

namespace ClosedStmtContinuationRegistry

/-- Read the statement continuation certificate as closed-fragment soundness. -/
theorem closedSoundness
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (R : ClosedStmtContinuationRegistry Γ σ st) :
    ClosedStmtSoundness σ st := by
  have hready : R.registry.readyForSoundness :=
    Continuation.ContinuationCertificate.get R.registry.certificate
  change StmtReadyForClosedSoundness Γ σ st
  exact R.ready_eq_closed ▸ hready

/-- Read the statement continuation certificate as no residual stuckness. -/
theorem noUnclassifiedStuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (R : ClosedStmtContinuationRegistry Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_of_closedStmtSoundness (closedSoundness R)

end ClosedStmtContinuationRegistry

namespace ClosedBlockContinuationRegistry

/-- Read the block continuation certificate as closed-fragment soundness. -/
theorem closedSoundness
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (R : ClosedBlockContinuationRegistry Γ σ body) :
    ClosedBlockSoundness σ body := by
  have hready : R.registry.readyForSoundness :=
    Continuation.ContinuationCertificate.get R.registry.certificate
  change BlockReadyForClosedSoundness Γ σ body
  exact R.ready_eq_closed ▸ hready

/-- Read the block continuation certificate as no residual stuckness. -/
theorem noUnclassifiedStuck
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (R : ClosedBlockContinuationRegistry Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_of_closedBlockSoundness (closedSoundness R)

end ClosedBlockContinuationRegistry

namespace ClosedFunctionBodyContinuationRegistry

/-- Read the function-body continuation certificate as closed-fragment soundness. -/
theorem closedSoundness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (R : ClosedFunctionBodyContinuationRegistry Γ σ body) :
    ClosedFunctionBodySoundness σ body := by
  have hready : R.registry.readyForSoundness :=
    Continuation.ContinuationCertificate.get R.registry.certificate
  change FunctionBodyReadyForClosedSoundness Γ σ body
  exact R.ready_eq_closed ▸ hready

/-- Read the function-body continuation certificate as no residual stuckness. -/
theorem noUnclassifiedStuck
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (R : ClosedFunctionBodyContinuationRegistry Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_of_closedFunctionBodySoundness
    (closedSoundness R)

end ClosedFunctionBodyContinuationRegistry

end Soundness
end Cpp3
