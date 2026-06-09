import CppFormalization.Cpp3.Soundness.ScopeReducedFinal
import CppFormalization.Cpp3.Soundness.Instantiate.LoopClassification

/-!
# CppFormalization.Cpp3.Soundness.LoopFinal

Final theorem surface after replacing while reentry soundness by a
`LoopClassificationTheorem`.

This is the next refinement after `ScopeReducedFinal`: local control handoffs are
corridor theorems, block close is a scope-exit corridor theorem, and while
same-syntax reentry is no longer exposed as a Soundness provider.  It is supplied
as a C++-facing loop-classification theorem.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- Provider bundle after replacing the last provider-shaped residual by a loop
classification theorem.

No field is an old Soundness provider anymore.  The remaining inputs are theorem
surfaces that lower layers should construct:

* local control corridors;
* scope-exit corridor;
* loop classification. -/
structure LoopClosedSoundnessProviders : Type where
  localCorridors : Instantiate.Easy.LocalControlCorridorTheorems
  scopeExit : Instantiate.ScopeExit.ScopeExitCorridorTheorem
  loopClassification : Instantiate.LoopClassification.LoopClassificationTheorem

/-- Reconstruct the scope-reduced final provider bundle from loop classification. -/
def scopeReducedClosedSoundnessProviders_of_loopClassification
    (P : LoopClosedSoundnessProviders) :
    ScopeReducedClosedSoundnessProviders where
  localCorridors := P.localCorridors
  scopeExit := P.scopeExit
  residual := {
    whileReentrySoundness :=
      Instantiate.LoopClassification.whileReentrySoundnessProvider_of_loopClassification
        P.loopClassification
  }

/-- Loop-final closed statement soundness theorem. -/
theorem closedStmtSoundness_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

/-- Loop-final closed block-body soundness theorem. -/
theorem closedBlockSoundness_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

/-- Loop-final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

/-- Loop-final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

/-- Loop-final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

/-- Loop-final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_loopClassified
    (P : LoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_scopeReduced
    (scopeReducedClosedSoundnessProviders_of_loopClassification P)
    boundary

end Final
end Soundness
end Cpp3
