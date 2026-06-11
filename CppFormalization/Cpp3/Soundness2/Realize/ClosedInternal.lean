import CppFormalization.Cpp3.Soundness2.Realize.Provider
import CppFormalization.Cpp3.Semantics.Kernel.ClassificationLemmas

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClosedInternal

Closed-internal realization and final application layer for Soundness2.

The flow in this file is intentionally linear:

* realized local-control / scope-exit / loop-behavior / classification pieces are
  assembled into a closed-internal provider;
* boundary sources are wrapped as closed-internal sources;
* the provider is applied to those sources to derive closed soundness;
* semantic classification lemmas turn closed soundness into no-unclassified-stuck.

This absorbs the old `Derive.ClosedInternal` role into `Realize`, so `Final` can
remain a thin public theorem surface over the realized route.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Assemble closed-internal provider sources from a named classification theorem
bundle. -/
def providerSources_of_classification
    (classification : Source.ClassificationSourceTheorems) :
    Source.ClosedInternalProviderSources where
  classification := classification

/-- Assemble closed-internal provider sources from realized local-control,
scope-exit, loop-behavior, and lower classification theorem bundles. -/
def providerSources_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_classification
    (classificationSourceTheorems_of_realization
      localControl scopeExit loopBehavior classification)

/-- Assemble closed-internal provider sources directly from a loop-behavior
component certifier. -/
def providerSources_of_componentRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    (classification : ClassificationRealizationTheorems) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_realization
    localControl
    scopeExit
    (loopBehaviorCertificateTheorem_of_componentTheorem loopBehavior)
    classification

/-- Realize a closed-internal statement source from a boundary source. -/
def stmtSource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundarySource : Source.StmtBoundarySource Γ σ st) :
    Source.ClosedInternalStmtSource Γ σ st where
  boundarySource := boundarySource

/-- Realize a closed-internal block source from a boundary source. -/
def blockSource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundarySource : Source.BlockBoundarySource Γ σ body) :
    Source.ClosedInternalBlockSource Γ σ body where
  boundarySource := boundarySource

/-- Realize a closed-internal function-body source from a function-body boundary
source. -/
def functionBodySource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundarySource : Source.FunctionBodyBoundarySource Γ σ body) :
    Source.ClosedInternalFunctionBodySource Γ σ body where
  boundarySource := boundarySource

/-- Statement soundness from closed-internal provider and source. -/
theorem closedStmtSoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.ClosedInternalStmtSource Γ σ st) :
    Source.ClosedStmtSoundness σ st :=
  Source.ClassificationSourceTheorems.classifyStmt P.classification source.boundarySource

/-- Block soundness from closed-internal provider and source. -/
theorem closedBlockSoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.ClosedInternalBlockSource Γ σ body) :
    Source.ClosedBlockSoundness σ body :=
  Source.ClassificationSourceTheorems.classifyBlock P.classification source.boundarySource

/-- Function-body soundness from closed-internal provider and source. -/
theorem closedFunctionBodySoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.ClosedInternalFunctionBodySource Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body :=
  Source.ClassificationSourceTheorems.classifyFunctionBody P.classification source.boundarySource

/-- No unclassified statement stuckness from statement soundness. -/
theorem noStmtUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.ClosedInternalStmtSource Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  Semantics.not_stmtUnclassifiedStuck_of_classified
    (closedStmtSoundness P source)

/-- No unclassified block stuckness from block soundness. -/
theorem noBlockUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.ClosedInternalBlockSource Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  Semantics.not_blockUnclassifiedStuck_of_classified
    (closedBlockSoundness P source)

/-- No unclassified function-body stuckness from function-body soundness. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.ClosedInternalFunctionBodySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  Semantics.not_functionBodyUnclassifiedStuck_of_classified
    (closedFunctionBodySoundness P source)

/-- Realized function-body soundness from realized provider pieces and a
function-body boundary source. -/
theorem closedFunctionBodySoundness_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness
    (providerSources_of_realization localControl scopeExit loopBehavior classification)
    (functionBodySource_of_boundarySource source)

/-- Realized function-body no-unclassified-stuck theorem from realized provider
pieces and a function-body boundary source. -/
theorem noFunctionBodyUnclassifiedStuck_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck
    (providerSources_of_realization localControl scopeExit loopBehavior classification)
    (functionBodySource_of_boundarySource source)

end Realize
end Soundness2
end Cpp3
