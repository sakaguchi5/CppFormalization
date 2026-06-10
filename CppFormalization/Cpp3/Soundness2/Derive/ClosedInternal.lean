import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Derive.ClosedInternal

Closed-internal derivations from provider/source theorem bundles.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

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
    ¬ Semantics.StmtUnclassifiedStuck σ st := by
  intro hstuck
  exact hstuck (closedStmtSoundness P source)

/-- No unclassified block stuckness from block soundness. -/
theorem noBlockUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.ClosedInternalBlockSource Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck (closedBlockSoundness P source)

/-- No unclassified function-body stuckness from function-body soundness. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.ClosedInternalFunctionBodySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck (closedFunctionBodySoundness P source)

end Derive
end Soundness2
end Cpp3
