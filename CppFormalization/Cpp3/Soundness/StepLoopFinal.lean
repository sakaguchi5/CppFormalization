import CppFormalization.Cpp3.Soundness.LoopFinal
import CppFormalization.Cpp3.Soundness.Instantiate.LoopEngine

/-!
# CppFormalization.Cpp3.Soundness.StepLoopFinal

Final theorem surface after constructing `LoopClassificationTheorem` from
`LoopSafetyFragment` plus step/derivation-height/coinductive classification
witnesses.

At this layer no old Soundness provider remains.  The inputs are all theorem
surfaces that lower layers must construct:

* local control corridors;
* scope-exit corridor;
* loop-safety + finite-step/coinductive loop classification engine.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- Final provider bundle after refining loop classification to the loop engine.

The `loopEngine` field is the refined source of while classification: it exposes
loop safety and the finite/coinductive classification witness rather than the old
provider-shaped while reentry assumption.
-/
structure StepLoopClosedSoundnessProviders : Type where
  localCorridors : Instantiate.Easy.LocalControlCorridorTheorems
  scopeExit : Instantiate.ScopeExit.ScopeExitCorridorTheorem
  loopEngine : Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem

/-- Reconstruct the previous loop-final bundle from the loop engine. -/
def loopClosedSoundnessProviders_of_stepCoinduction
    (P : StepLoopClosedSoundnessProviders) :
    LoopClosedSoundnessProviders where
  localCorridors := P.localCorridors
  scopeExit := P.scopeExit
  loopClassification :=
    Instantiate.LoopClassification.loopClassificationTheorem_of_stepCoinduction
      P.loopEngine

/-- Step/coinduction-final closed statement soundness theorem. -/
theorem closedStmtSoundness_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

/-- Step/coinduction-final closed block-body soundness theorem. -/
theorem closedBlockSoundness_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

/-- Step/coinduction-final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

/-- Step/coinduction-final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

/-- Step/coinduction-final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

/-- Step/coinduction-final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_stepLoop
    (P : StepLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_loopClassified
    (loopClosedSoundnessProviders_of_stepCoinduction P)
    boundary

end Final
end Soundness
end Cpp3
