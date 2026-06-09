import CppFormalization.Cpp3.Soundness.Final
import CppFormalization.Cpp3.Soundness.Instantiate.Easy

/-!
# CppFormalization.Cpp3.Soundness.ReducedFinal

Reduced final theorem surface after theoremizing the easy local-control providers.

The old final theorem surface required seven provider components after expansion.
This file keeps only the two genuinely hard residual semantic providers explicit:

* block scope close after an opened block body has run;
* while reentry classification for the same while statement at a reentry state.

All other local-control provider slots are filled by theoremized corridor-to-
continuation conversions from `Instantiate.Easy`.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- The two residual providers that are not local corridor glue.

`blockClose` is a scope/lifetime-exit fact.  `whileReentrySoundness` is a loop
classification fact for a same-syntax while backedge. -/
structure ResidualSemanticProviders : Type where
  blockClose : Instantiate.BlockCloseProvider
  whileReentrySoundness : Structural.WhileReentrySoundnessProvider

/-- Reduced final provider bundle.

The easy part is no longer a Soundness-provider bundle.  It is a collection of
lower-layer corridor theorems from which the old provider slots are constructed. -/
structure ReducedClosedSoundnessProviders : Type where
  localCorridors : Instantiate.Easy.LocalControlCorridorTheorems
  residual : ResidualSemanticProviders

/-- Reconstruct the old final provider bundle from the reduced one. -/
def closedSoundnessProviders_of_reduced
    (P : ReducedClosedSoundnessProviders) :
    ClosedSoundnessProviders where
  firstFive :=
    Instantiate.Easy.firstFiveProviders_of_easy
      P.localCorridors
      P.residual.blockClose
  whileClause :=
    Instantiate.Easy.whileClauseProviders_of_easy
      P.localCorridors
  whileReentrySoundness := P.residual.whileReentrySoundness

/-- Reduced final closed statement soundness theorem. -/
theorem closedStmtSoundness_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness
    (closedSoundnessProviders_of_reduced P)
    boundary

/-- Reduced final closed block-body soundness theorem. -/
theorem closedBlockSoundness_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness
    (closedSoundnessProviders_of_reduced P)
    boundary

/-- Reduced final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness
    (closedSoundnessProviders_of_reduced P)
    boundary

/-- Reduced final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck
    (closedSoundnessProviders_of_reduced P)
    boundary

/-- Reduced final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck
    (closedSoundnessProviders_of_reduced P)
    boundary

/-- Reduced final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_reduced
    (P : ReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck
    (closedSoundnessProviders_of_reduced P)
    boundary

end Final
end Soundness
end Cpp3
