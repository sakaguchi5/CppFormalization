import CppFormalization.Cpp3.Soundness.StepLoopFinal
import CppFormalization.Cpp3.Soundness.Derive.LocalCorridors

/-!
# CppFormalization.Cpp3.Soundness.DerivedLocalFinal

Final theorem surface after concretizing `localCorridors`.

`StepLoopFinal` still accepted `localCorridors` as the Easy theorem bundle.  This
file replaces that field with the lower-layer local-control construction theorem
bundle from `Soundness.Derive.LocalCorridors`.

The remaining final inputs are therefore:

* concrete local-control construction facts;
* the scope-exit corridor theorem;
* the loop-safety + step/coinduction loop engine theorem.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- Final bundle after concretizing the local-control corridor input.

No old Soundness provider appears here.  The `localControl` field is already a
lower-layer construction bundle, not an Easy corridor bundle. -/
structure DerivedLocalClosedSoundnessProviders : Type where
  localControl : Derive.LocalCorridors.LocalControlConstructionTheorems
  scopeExit : Instantiate.ScopeExit.ScopeExitCorridorTheorem
  loopEngine : Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem

/-- Reconstruct `StepLoopFinal`'s provider bundle from concrete local-control facts. -/
def stepLoopClosedSoundnessProviders_of_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders) :
    StepLoopClosedSoundnessProviders where
  localCorridors :=
    Derive.LocalCorridors.localControlCorridorTheorems_of_construction
      P.localControl
  scopeExit := P.scopeExit
  loopEngine := P.loopEngine

/-- Derived-local final closed statement soundness theorem. -/
theorem closedStmtSoundness_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

/-- Derived-local final closed block-body soundness theorem. -/
theorem closedBlockSoundness_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

/-- Derived-local final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

/-- Derived-local final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

/-- Derived-local final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

/-- Derived-local final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_derivedLocal
    (P : DerivedLocalClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_stepLoop
    (stepLoopClosedSoundnessProviders_of_derivedLocal P)
    boundary

end Final
end Soundness
end Cpp3
