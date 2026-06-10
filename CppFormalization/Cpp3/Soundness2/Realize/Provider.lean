import CppFormalization.Cpp3.Soundness2.Realize.Stability
import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Provider

Realization theorem/def layer for provider/source theorem bundles.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realize a local-control seq source from sequence-tail stability. -/
def seqTailControlSource_of_stability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (stability : Stability.SeqTailStability Γ Θ σ σ₁ head tail) :
    Source.SeqTailControlSource Γ Θ σ σ₁ head tail where
  stability := stability

/-- Realize a local-control block-tail source from block-tail stability. -/
def blockTailControlSource_of_stability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (stability : Stability.BlockTailStability Γ Θ σ σ₁ head tail) :
    Source.BlockTailControlSource Γ Θ σ σ₁ head tail where
  stability := stability

/-- Realize a local-control selected-branch source from selected-branch stability. -/
def selectedBranchControlSource_of_stability
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side) :
    Source.SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch side where
  stability := stability

/-- Realized selected-branch stability, keeping the selected side explicit. -/
inductive SelectedBranchStabilitySelection
    (Γ : TypeEnv) (σ : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  | thenSelected
      {Γc : TypeEnv} {σc : State}
      (stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch
        .thenBranch) :
      SelectedBranchStabilitySelection Γ σ cond thenBranch elseBranch
  | elseSelected
      {Γc : TypeEnv} {σc : State}
      (stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch
        .elseBranch) :
      SelectedBranchStabilitySelection Γ σ cond thenBranch elseBranch

namespace SelectedBranchStabilitySelection

/-- Convert selected-branch stability selection into the local-control selection. -/
def toControlSelection
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (h : SelectedBranchStabilitySelection Γ σ cond thenBranch elseBranch) :
    Source.SelectedBranchControlSelection Γ σ cond thenBranch elseBranch :=
  match h with
  | .thenSelected stability =>
      .thenSelected (selectedBranchControlSource_of_stability stability)
  | .elseSelected stability =>
      .elseSelected (selectedBranchControlSource_of_stability stability)

end SelectedBranchStabilitySelection

/-- Realize a while-body-entry source from its lower body boundary. -/
def loopBodyEntryControlSource_of_boundary
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.whileStmt cond body))
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (condTrue : Semantics.BigStepCond σ cond true σc)
    (bodyBoundary : Boundary.StmtBoundary Γc σc body) :
    Source.LoopBodyEntryControlSource Γ Γc σ σc cond body where
  source := source
  condition := condition
  condTrue := condTrue
  bodyBoundary := bodyBoundary

/-- Realize a while-backedge source from lower while-boundary stability and
continuation evidence. -/
def loopBackedgeControlSource_of_components
    {Γ Γc : TypeEnv} {σ σreentry : State} {cond : CppCond} {body : CppStmt}
    {Reentry : Prop}
    (stability : Stability.WhileBoundaryStability Γ Γc σ cond body)
    (reentryEq : Stability.WhileBoundaryStability.routePostState stability = σreentry)
    (reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body))
    (certificate : Continuation.ContinuationCertificate Reentry) :
    Source.LoopBackedgeControlSource Γ Γc σ σreentry cond body Reentry where
  stability := stability
  reentryEq := reentryEq
  reentryBoundary := reentryBoundary
  certificate := certificate

/-- Build the seq source theorem from a lower stability-producing theorem. -/
def seqTailControlSourceTheorem_of_stabilityTheorem
    (produce :
      ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
        Boundary.StmtBoundary Γ σ (.seq head tail) →
        Semantics.SeqNormalRoute σ σ₁ head tail →
          Σ Θ : TypeEnv,
            Stability.SeqTailStability Γ Θ σ σ₁ head tail) :
    Source.SeqTailControlSourceTheorem where
  source := by
    intro Γ σ σ₁ head tail boundary route
    rcases produce boundary route with ⟨Θ, stability⟩
    exact ⟨Θ, seqTailControlSource_of_stability stability⟩

/-- Build the block-tail source theorem from a lower stability-producing theorem. -/
def blockTailControlSourceTheorem_of_stabilityTheorem
    (produce :
      ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
        Boundary.BlockBoundary Γ σ (.cons head tail) →
        Semantics.BlockConsNormalRoute σ σ₁ head tail →
          Σ Θ : TypeEnv,
            Stability.BlockTailStability Γ Θ σ σ₁ head tail) :
    Source.BlockTailControlSourceTheorem where
  source := by
    intro Γ σ σ₁ head tail boundary route
    rcases produce boundary route with ⟨Θ, stability⟩
    exact ⟨Θ, blockTailControlSource_of_stability stability⟩

/-- Build the selected-branch source theorem from a lower selected-branch theorem. -/
def selectedBranchControlSourceTheorem_of_stabilityTheorem
    (select :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond}
        {thenBranch elseBranch : CppStmt},
        Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
          SelectedBranchStabilitySelection Γ σ cond thenBranch elseBranch) :
    Source.SelectedBranchControlSourceTheorem where
  select := by
    intro Γ σ cond thenBranch elseBranch boundary
    exact (select boundary).toControlSelection

/-- Build the while-body-entry source theorem from a lower body-boundary theorem. -/
def loopBodyEntryControlSourceTheorem_of_boundaryTheorem
    (produce :
      ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Boundary.CondBoundary Γ Γc σ cond →
        Semantics.BigStepCond σ cond true σc →
          Boundary.StmtBoundary Γc σc body) :
    Source.LoopBodyEntryControlSourceTheorem where
  source := by
    intro Γ Γc σ σc cond body boundary condition condTrue
    exact loopBodyEntryControlSource_of_boundary boundary condition condTrue
      (produce boundary condition condTrue)

/-- Build the while-backedge source theorem from lower backedge-producing theorems. -/
def loopBackedgeControlSourceTheorem_of_backedgeTheorems
    (bodyNormal :
      ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Boundary.CondBoundary Γ Γc σ cond →
        Semantics.BigStepCond σ cond true σc →
        Boundary.StmtBoundary Γc σc body →
        Semantics.BigStepStmt σc body .normal σb →
          Σ Reentry : Prop,
            Source.LoopBackedgeControlSource Γ Γc σ σb cond body Reentry)
    (bodyContinue :
      ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Boundary.CondBoundary Γ Γc σ cond →
        Semantics.BigStepCond σ cond true σc →
        Boundary.StmtBoundary Γc σc body →
        Semantics.BigStepStmt σc body .continueResult σb →
          Σ Reentry : Prop,
            Source.LoopBackedgeControlSource Γ Γc σ σb cond body Reentry) :
    Source.LoopBackedgeControlSourceTheorem where
  bodyNormal := bodyNormal
  bodyContinue := bodyContinue

/-- Realizer bundle for all local-control source theorems. -/
structure LocalControlRealizationTheorems : Type where
  seq : Source.SeqTailControlSourceTheorem
  blockTail : Source.BlockTailControlSourceTheorem
  branch : Source.SelectedBranchControlSourceTheorem
  whileBody : Source.LoopBodyEntryControlSourceTheorem
  whileBackedge : Source.LoopBackedgeControlSourceTheorem

namespace LocalControlRealizationTheorems

/-- Convert realized local-control theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : LocalControlRealizationTheorems) :
    Source.LocalControlSourceTheorems where
  seq := R.seq
  blockTail := R.blockTail
  branch := R.branch
  whileBody := R.whileBody
  whileBackedge := R.whileBackedge

end LocalControlRealizationTheorems

/-- Realize a scope-exit block-close source from block-close stability. -/
def blockCloseSource_of_stability
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (closeStability : Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body) :
    Source.BlockCloseSource Γ Γopen Θ Δ σbody σclosed body where
  closeStability := closeStability

/-- Build the scope-exit source theorem from a lower block-close-stability theorem. -/
def blockCloseSourceTheorem_of_stabilityTheorem
    (close :
      ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
        {r : CtrlResult} {σbody : State},
        Boundary.StmtBoundary Γ σ (.block body) →
        Boundary.BlockBoundary Γopen σopened body →
        Semantics.OpenedBlockRoute σ σopened body →
        Semantics.BigStepBlock σopened body r σbody →
          Σ Θ : TypeEnv,
            Σ Δ : TypeEnv,
              Σ σclosed : State,
                Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body) :
    Source.BlockCloseSourceTheorem where
  close := by
    intro Γ Γopen σ σopened body r σbody blockBoundary openedBody openedRoute bodyStep
    rcases close blockBoundary openedBody openedRoute bodyStep with
      ⟨Θ, Δ, σclosed, closeStability⟩
    exact ⟨Θ, Δ, σclosed, blockCloseSource_of_stability closeStability⟩

/-- Realizer bundle for scope-exit source theorems. -/
structure ScopeExitRealizationTheorems : Type where
  blockClose : Source.BlockCloseSourceTheorem

namespace ScopeExitRealizationTheorems

/-- Convert realized scope-exit theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : ScopeExitRealizationTheorems) :
    Source.ScopeExitSourceTheorems where
  blockClose := R.blockClose

end ScopeExitRealizationTheorems

/-- Lower realization source for a while behavior certificate. -/
structure LoopBehaviorComponentSource
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : Source.LoopBehaviorSource σ cond body

namespace LoopBehaviorComponentSource

/-- Convert lower loop-behavior components into the behavior certificate. -/
def toCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificate Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  behavior := h.behavior

end LoopBehaviorComponentSource

/-- Build the loop-behavior theorem from a lower behavior-component certifier. -/
def loopBehaviorCertificateTheorem_of_componentTheorem
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificateTheorem where
  certify := by
    intro Γ σ cond body boundary
    rcases certify boundary with ⟨Γc, source⟩
    exact ⟨Γc, source.toCertificate⟩

/-- Lower classification realizer bundle. -/
structure ClassificationRealizationTheorems : Type where
  stmtClassify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Source.StmtBoundarySource Γ σ st →
        Source.ClosedStmtSoundness σ st
  blockClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.BlockBoundarySource Γ σ body →
        Source.ClosedBlockSoundness σ body
  functionBodyClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

/-- Assemble the named classification source theorem bundle. -/
def classificationSourceTheorems_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClassificationSourceTheorems where
  localControl := localControl.toSourceTheorems
  scopeExit := scopeExit.toSourceTheorems
  loopBehavior := loopBehavior
  stmtClassify := classification.stmtClassify
  blockClassify := classification.blockClassify
  functionBodyClassify := classification.functionBodyClassify

end Realize
end Soundness2
end Cpp3
