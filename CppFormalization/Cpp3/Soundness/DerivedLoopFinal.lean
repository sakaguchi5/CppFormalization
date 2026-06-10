import CppFormalization.Cpp3.Soundness.DerivedScopeFinal
import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.Certificate

/-!
# CppFormalization.Cpp3.Soundness.DerivedLoopFinal

Final theorem surface after replacing the boundary-only loop split with a
certificate-driven loop-progress theorem.

`DerivedScopeFinal` still accepted `loopEngine` as the monolithic
`LoopSafetyStepCoinductionTheorem`.  The previous derived-loop layer replaced
that field with a finite/divergent case split.  This file refines the target one
step further: the loop side now asks for an explicit progress certificate theorem,
so the finite-vs-divergent explanation is not hidden inside a boundary-only
classifier.

The remaining final inputs are therefore all lower-layer construction surfaces:

* local-control construction facts;
* scope-exit construction facts;
* certificate-driven finite/divergent loop-progress classification.
-/

namespace Cpp3
namespace Soundness
namespace Final

/-- Final bundle after making the loop engine certificate-driven. -/
structure DerivedLoopClosedSoundnessProviders : Type where
  localControl : Derive.LocalCorridors.LocalControlConstructionTheorems
  scopeExit : Derive.ScopeExit.ScopeExitConstructionTheorems
  loopProgress : Derive.LoopEngine.LoopProgressCertificateTheorem

/-- Reconstruct `DerivedScopeFinal`'s provider bundle from the certificate-driven
loop-progress theorem. -/
def derivedScopeClosedSoundnessProviders_of_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders) :
    DerivedScopeClosedSoundnessProviders where
  localControl := P.localControl
  scopeExit := P.scopeExit
  loopEngine :=
    Derive.LoopEngine.loopSafetyStepCoinductionTheorem_of_progressCertificate
      P.loopProgress

/-- Derived-loop final closed statement soundness theorem. -/
theorem closedStmtSoundness_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  closedStmtSoundness_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

/-- Derived-loop final closed block-body soundness theorem. -/
theorem closedBlockSoundness_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  closedBlockSoundness_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

/-- Derived-loop final closed function-body soundness theorem. -/
theorem closedFunctionBodySoundness_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

/-- Derived-loop final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

/-- Derived-loop final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

/-- Derived-loop final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck_derivedLoop
    (P : DerivedLoopClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_derivedScope
    (derivedScopeClosedSoundnessProviders_of_derivedLoop P)
    boundary

end Final
end Soundness
end Cpp3
