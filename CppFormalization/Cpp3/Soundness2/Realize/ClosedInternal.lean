import CppFormalization.Cpp3.Soundness2.Realize.Provider

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClosedInternal

Realization-to-source assembly for the closed internal fragment.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Assemble closed-internal provider sources from realized local-control,
scope-exit, loop-behavior, and classification theorem bundles. -/
def providerSources_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClosedInternalProviderSources where
  localControl := localControl.toSourceTheorems
  scopeExit := scopeExit.toSourceTheorems
  loopBehavior := loopBehavior
  stmtClassify := classification.stmtClassify
  blockClassify := classification.blockClassify
  functionBodyClassify := classification.functionBodyClassify

/-- Assemble closed-internal provider sources directly from a loop-behavior component
certifier. -/
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

/-- Realize a closed-internal function-body source from a function-body boundary source. -/
def functionBodySource_of_boundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundarySource : Source.FunctionBodyBoundarySource Γ σ body) :
    Source.ClosedInternalFunctionBodySource Γ σ body where
  boundarySource := boundarySource

/-- Realize a closed-internal statement source directly from lower statement
components. -/
def stmtSource_of_components
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Source.ClosedInternalStmtSource Γ σ st :=
  stmtSource_of_boundarySource
    (stmtBoundarySource_of_formed typed formed safety entry)

/-- Realize a closed-internal block source directly from lower block components. -/
def blockSource_of_components
    {Γ : TypeEnv} {σ : State} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Source.ClosedInternalBlockSource Γ σ body :=
  blockSource_of_boundarySource
    (blockBoundarySource_of_formed typed formed safety entry)

/-- Realize a closed-internal function-body source from a statement boundary source
and the function-body static control surface. -/
def functionBodySource_of_stmtSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (stmtSource : Source.StmtBoundarySource Γ σ body) :
    Source.ClosedInternalFunctionBodySource Γ σ body :=
  functionBodySource_of_boundarySource
    (functionBodyBoundarySource_of_stmtSource typed static stmtSource)

end Realize
end Soundness2
end Cpp3
