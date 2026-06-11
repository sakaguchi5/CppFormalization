import CppFormalization.Cpp3.Soundness2.Realize.Stability
import CppFormalization.Cpp3.Soundness2.Source.LocalControl

/-!
# CppFormalization.Cpp3.Soundness2.Realize.LocalControl

Realized local-control theorem bundle for the closed-internal Soundness2 route.

This layer is no longer just a record of assumptions: it also restores the
lower-evidence bridge from stability packages to the local-control source
objects consumed by boundary classification.
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

/-- Build the while-body source theorem from a lower body-boundary theorem. -/
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

end Realize
end Soundness2
end Cpp3
