import CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

/-!
# CppFormalization.Cpp3.Soundness2.Source.Classification

Classification source vocabulary for Soundness2.

This file is the replacement for the raw classification fields that originally
lived directly in `ClosedInternalProviderSources`.  Classification is now its own
source theorem bundle, tied to the local-control, scope-exit, and loop-behavior
sources that explain why the classifier is the correct closed-internal one.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Soundness target for a closed internal statement. -/
abbrev ClosedStmtSoundness (σ : State) (st : CppStmt) : Prop :=
  Semantics.StmtClassified σ st

/-- Soundness target for a closed internal block body. -/
abbrev ClosedBlockSoundness (σ : State) (body : StmtBlock) : Prop :=
  Semantics.BlockClassified σ body

/-- Soundness target for a closed internal function body. -/
abbrev ClosedFunctionBodySoundness (σ : State) (body : CppStmt) : Prop :=
  Semantics.FunctionBodyClassified σ body

/-- Classification source theorem bundle.

The classifier is not hidden inside `ClosedInternalProviderSources` anymore.  It
is a named source theorem layer whose premises are the C++-meaningful local
control, scope-exit, and loop-behavior theorem surfaces.  This keeps the final
closed-internal provider clean while still making the remaining classification
work explicit. -/
structure ClassificationSourceTheorems : Type where
  localControl : LocalControlSourceTheorems
  scopeExit : ScopeExitSourceTheorems
  loopBehavior : LoopBehaviorCertificateTheorem
  stmtClassify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      StmtBoundarySource Γ σ st →
        ClosedStmtSoundness σ st
  blockClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      BlockBoundarySource Γ σ body →
        ClosedBlockSoundness σ body
  functionBodyClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      FunctionBodyBoundarySource Γ σ body →
        ClosedFunctionBodySoundness σ body

namespace ClassificationSourceTheorems

/-- Project statement classification. -/
def classifyStmt
    (P : ClassificationSourceTheorems)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : StmtBoundarySource Γ σ st) :
    ClosedStmtSoundness σ st :=
  P.stmtClassify source

/-- Project block classification. -/
def classifyBlock
    (P : ClassificationSourceTheorems)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : BlockBoundarySource Γ σ body) :
    ClosedBlockSoundness σ body :=
  P.blockClassify source

/-- Project function-body classification. -/
def classifyFunctionBody
    (P : ClassificationSourceTheorems)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : FunctionBodyBoundarySource Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  P.functionBodyClassify source

end ClassificationSourceTheorems

end Source
end Soundness2
end Cpp3
