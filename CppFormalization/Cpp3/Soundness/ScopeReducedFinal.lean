import CppFormalization.Cpp3.Soundness.ReducedFinal
import CppFormalization.Cpp3.Soundness.Instantiate.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness.ScopeReducedFinal

Final theorem surface after replacing `BlockCloseProvider` by
`ScopeExitCorridorTheorem`.

At this layer the only remaining semantic provider is while reentry
classification.  Block scope close is no longer a Soundness provider; it is a
C++ scope/lifetime corridor theorem that reconstructs the old provider interface.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- The residual provider after block-close has been reduced to a scope-exit corridor.

This is now only the while same-syntax backedge classification problem. -/
structure ScopeReducedResidualProviders : Type where
  whileReentrySoundness : Structural.WhileReentrySoundnessProvider

/-- Provider bundle for the scope-reduced final theorem surface.

`localCorridors` covers the easy local control handoffs, `scopeExit` covers block
scope closing, and the only still-provider-shaped semantic component is while
reentry soundness. -/
structure ScopeReducedClosedSoundnessProviders : Type where
  localCorridors : Instantiate.Easy.LocalControlCorridorTheorems
  scopeExit : Instantiate.ScopeExit.ScopeExitCorridorTheorem
  residual : ScopeReducedResidualProviders

/-- Reconstruct the previous reduced provider bundle from a scope-exit corridor. -/
def reducedClosedSoundnessProviders_of_scopeExit
    (P : ScopeReducedClosedSoundnessProviders) :
    ReducedClosedSoundnessProviders where
  localCorridors := P.localCorridors
  residual := {
    blockClose := Instantiate.ScopeExit.blockCloseProvider_of_scopeExit P.scopeExit
    whileReentrySoundness := P.residual.whileReentrySoundness
  }

/-- Scope-reduced final closed statement soundness theorem. -/
theorem closedStmtSoundness_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

/-- Scope-reduced final closed block-body soundness theorem. -/
theorem closedBlockSoundness_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

/-- Scope-reduced final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

/-- Scope-reduced final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

/-- Scope-reduced final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

/-- Scope-reduced final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_scopeReduced
    (P : ScopeReducedClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_reduced
    (reducedClosedSoundnessProviders_of_scopeExit P)
    boundary

end Final
end Soundness
end Cpp3
