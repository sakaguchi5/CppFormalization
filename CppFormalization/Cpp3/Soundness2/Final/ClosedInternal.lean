import CppFormalization.Cpp3.Soundness2.Derive.ClosedInternal
import CppFormalization.Cpp3.Soundness2.Realize.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Final.ClosedInternal

Final closed-internal theorem surface for Soundness2.

This file imports no old `Cpp3.Soundness` and no old top-level `Cpp3.Realization`.
-/

namespace Cpp3
namespace Soundness2
namespace Final

/-- Final Soundness2 statement soundness theorem. -/
theorem closedStmtSoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.ClosedInternalStmtSource Γ σ st) :
    Source.ClosedStmtSoundness σ st :=
  Derive.closedStmtSoundness P source

/-- Final Soundness2 block soundness theorem. -/
theorem closedBlockSoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.ClosedInternalBlockSource Γ σ body) :
    Source.ClosedBlockSoundness σ body :=
  Derive.closedBlockSoundness P source

/-- Final Soundness2 function-body soundness theorem. -/
theorem closedFunctionBodySoundness
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.ClosedInternalFunctionBodySource Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body :=
  Derive.closedFunctionBodySoundness P source

/-- Final Soundness2 statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.ClosedInternalStmtSource Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  Derive.noStmtUnclassifiedStuck P source

/-- Final Soundness2 block no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.ClosedInternalBlockSource Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  Derive.noBlockUnclassifiedStuck P source

/-- Final Soundness2 function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : Source.ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.ClosedInternalFunctionBodySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  Derive.noFunctionBodyUnclassifiedStuck P source

/-- Convenience final theorem from realized provider/source components. -/
theorem closedFunctionBodySoundness_of_realization
    (localControl : Realize.LocalControlRealizationTheorems)
    (scopeExit : Realize.ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : Realize.ClassificationRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body :=
  closedFunctionBodySoundness
    (Realize.providerSources_of_realization localControl scopeExit loopBehavior classification)
    (Realize.functionBodySource_of_boundarySource source)

/-- Convenience final no-stuck theorem from realized provider/source components. -/
theorem noFunctionBodyUnclassifiedStuck_of_realization
    (localControl : Realize.LocalControlRealizationTheorems)
    (scopeExit : Realize.ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : Realize.ClassificationRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck
    (Realize.providerSources_of_realization localControl scopeExit loopBehavior classification)
    (Realize.functionBodySource_of_boundarySource source)

end Final
end Soundness2
end Cpp3
