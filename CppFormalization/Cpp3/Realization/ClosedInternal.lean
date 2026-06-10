import CppFormalization.Cpp3.Realization.ProviderSource
import CppFormalization.Cpp3.Soundness.Derive.ClosedInternalFinal

/-!
# CppFormalization.Cpp3.Realization.ClosedInternal

Realization-to-Soundness bridge for the closed internal fragment.

`Soundness.Derive.ClosedInternalFinal` consumes closed-internal provider sources
and boundary sources.  This file theoremizes the final realization step: lower
realizer bundles and realized boundary sources are converted into the exact
closed-internal sources expected by Soundness, and then the final soundness/no-
stuck theorems are projected.
-/

namespace Cpp3
namespace Realization
namespace ClosedInternal

/-- Assemble closed-internal provider sources from realized local-control,
scope-exit, and loop-behavior theorem bundles. -/
def providerSources_of_realization
    (localControl : ProviderSource.LocalControlRealizationTheorems)
    (scopeExit : ProviderSource.ScopeExitRealizationTheorems)
    (loopBehavior : Soundness.Derive.LoopEngine.LoopBehaviorCertificateTheorem) :
    Soundness.Derive.ClosedInternal.ClosedInternalProviderSources where
  localControl := localControl.toSourceTheorems
  scopeExit := scopeExit.toSourceTheorems
  loopBehavior := loopBehavior

/-- Assemble closed-internal provider sources directly from a lower
loop-behavior component certifier. -/
def providerSources_of_componentRealization
    (localControl : ProviderSource.LocalControlRealizationTheorems)
    (scopeExit : ProviderSource.ScopeExitRealizationTheorems)
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            ProviderSource.LoopBehaviorComponentSource Γ Γc σ cond body) :
    Soundness.Derive.ClosedInternal.ClosedInternalProviderSources :=
  providerSources_of_realization
    localControl
    scopeExit
    (ProviderSource.loopBehaviorCertificateTheorem_of_componentTheorem loopBehavior)

/-- Realize a closed-internal statement source from a Phase-4 statement boundary
source. -/
def stmtSource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundarySource : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ st) :
    Soundness.Derive.ClosedInternal.ClosedInternalStmtSource Γ σ st where
  boundarySource := boundarySource

/-- Realize a closed-internal block source from a Phase-4 block boundary source. -/
def blockSource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundarySource : Soundness.Derive.BoundaryConstruction.BlockBoundarySource Γ σ body) :
    Soundness.Derive.ClosedInternal.ClosedInternalBlockSource Γ σ body where
  boundarySource := boundarySource

/-- Realize a closed-internal function-body source from a Phase-4 function-body
boundary source. -/
def functionBodySource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundarySource : Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body) :
    Soundness.Derive.ClosedInternal.ClosedInternalFunctionBodySource Γ σ body where
  boundarySource := boundarySource

/-- Realize a closed-internal statement source directly from lower statement
components. -/
def stmtSource_of_components
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Soundness.Derive.ClosedInternal.ClosedInternalStmtSource Γ σ st :=
  stmtSource_of_boundarySource
    (BoundarySource.stmtBoundarySource_of_formed typed formed safety entry)

/-- Realize a closed-internal block source directly from lower block components. -/
def blockSource_of_components
    {Γ : TypeEnv} {σ : State} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Soundness.Derive.ClosedInternal.ClosedInternalBlockSource Γ σ body :=
  blockSource_of_boundarySource
    (BoundarySource.blockBoundarySource_of_formed typed formed safety entry)

/-- Realize a closed-internal function-body source from a statement boundary
source and the function-body static control surface. -/
def functionBodySource_of_stmtSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (stmtSource : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ body) :
    Soundness.Derive.ClosedInternal.ClosedInternalFunctionBodySource Γ σ body :=
  functionBodySource_of_boundarySource
    (BoundarySource.functionBodyBoundarySource_of_stmtSource typed static stmtSource)

/-- Closed-internal statement soundness from realized provider and statement
sources. -/
theorem closedStmtSoundness
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ st) :
    Soundness.ClosedStmtSoundness σ st :=
  Soundness.Derive.ClosedInternal.closedStmtSoundness P
    (stmtSource_of_boundarySource source)

/-- Closed-internal block soundness from realized provider and block sources. -/
theorem closedBlockSoundness
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Soundness.Derive.BoundaryConstruction.BlockBoundarySource Γ σ body) :
    Soundness.ClosedBlockSoundness σ body :=
  Soundness.Derive.ClosedInternal.closedBlockSoundness P
    (blockSource_of_boundarySource source)

/-- Closed-internal function-body soundness from realized provider and
function-body sources. -/
theorem closedFunctionBodySoundness
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body) :
    Soundness.ClosedFunctionBodySoundness σ body :=
  Soundness.Derive.ClosedInternal.closedFunctionBodySoundness P
    (functionBodySource_of_boundarySource source)

/-- Closed-internal statement no-unclassified-stuck theorem from realized
sources. -/
theorem noStmtUnclassifiedStuck
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  Soundness.Derive.ClosedInternal.noStmtUnclassifiedStuck P
    (stmtSource_of_boundarySource source)

/-- Closed-internal block no-unclassified-stuck theorem from realized sources. -/
theorem noBlockUnclassifiedStuck
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Soundness.Derive.BoundaryConstruction.BlockBoundarySource Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  Soundness.Derive.ClosedInternal.noBlockUnclassifiedStuck P
    (blockSource_of_boundarySource source)

/-- Closed-internal function-body no-unclassified-stuck theorem from realized
sources. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : Soundness.Derive.ClosedInternal.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  Soundness.Derive.ClosedInternal.noFunctionBodyUnclassifiedStuck P
    (functionBodySource_of_boundarySource source)

/-- Convenience theorem: function-body soundness directly from local/scope/loop
realizers and a realized function-body boundary source. -/
theorem closedFunctionBodySoundness_of_realization
    (localControl : ProviderSource.LocalControlRealizationTheorems)
    (scopeExit : ProviderSource.ScopeExitRealizationTheorems)
    (loopBehavior : Soundness.Derive.LoopEngine.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body) :
    Soundness.ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness
    (providerSources_of_realization localControl scopeExit loopBehavior)
    source

/-- Convenience theorem: no unclassified stuck directly from local/scope/loop
realizers and a realized function-body boundary source. -/
theorem noFunctionBodyUnclassifiedStuck_of_realization
    (localControl : ProviderSource.LocalControlRealizationTheorems)
    (scopeExit : ProviderSource.ScopeExitRealizationTheorems)
    (loopBehavior : Soundness.Derive.LoopEngine.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck
    (providerSources_of_realization localControl scopeExit loopBehavior)
    source

end ClosedInternal
end Realization
end Cpp3
