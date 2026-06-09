import CppFormalization.Cpp3.Soundness.DerivedLocalFinal
import CppFormalization.Cpp3.Soundness.Derive.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness.DerivedScopeFinal

Final theorem surface after concretizing both local corridors and scope exit.

`DerivedLocalFinal` already replaced `localCorridors` with lower-layer local
control construction facts.  This file also replaces the `scopeExit` input with
lower-layer block-close stability construction facts from
`Soundness.Derive.ScopeExit`.

The remaining final input is therefore only the loop-safety +
step/coinduction loop engine theorem.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- Final bundle after concretizing local-control corridors and block scope exit.

No old Soundness provider appears here.  The `scopeExit` field is now a concrete
construction bundle over `Stability.BlockCloseStability`, not the higher
`Instantiate.ScopeExit.ScopeExitCorridorTheorem` interface.
-/
structure DerivedScopeClosedSoundnessProviders : Type where
  localControl : Derive.LocalCorridors.LocalControlConstructionTheorems
  scopeExit : Derive.ScopeExit.ScopeExitConstructionTheorems
  loopEngine : Instantiate.LoopClassification.LoopSafetyStepCoinductionTheorem

/-- Reconstruct `DerivedLocalFinal`'s bundle from concrete scope-exit facts. -/
def derivedLocalClosedSoundnessProviders_of_derivedScope
    (P : DerivedScopeClosedSoundnessProviders) :
    DerivedLocalClosedSoundnessProviders where
  localControl := P.localControl
  scopeExit :=
    Derive.ScopeExit.scopeExitCorridorTheorem_of_construction
      P.scopeExit
  loopEngine := P.loopEngine

/-- Derived-scope final closed statement soundness theorem. -/
theorem closedStmtSoundness_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

/-- Derived-scope final closed block-body soundness theorem. -/
theorem closedBlockSoundness_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

/-- Derived-scope final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

/-- Derived-scope final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

/-- Derived-scope final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

/-- Derived-scope final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_derivedScope
    (P : DerivedScopeClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_derivedLocal
    (derivedLocalClosedSoundnessProviders_of_derivedScope P)
    boundary

end Final
end Soundness
end Cpp3
