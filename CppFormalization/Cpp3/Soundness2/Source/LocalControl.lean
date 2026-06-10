import CppFormalization.Cpp3.Soundness2.Source.Stability
import CppFormalization.Cpp3.Continuation.All

/-!
# CppFormalization.Cpp3.Soundness2.Source.LocalControl

Source theorem vocabulary for local control handoffs.

This file contains no final soundness proof.  It only names the lower local-control
theorems that later derivation/final layers consume.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Source for a sequence-tail local-control handoff. -/
structure SeqTailControlSource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  stability : Stability.SeqTailStability Γ Θ σ σ₁ head tail

namespace SeqTailControlSource

/-- Project the sequence-tail stability package. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailControlSource Γ Θ σ σ₁ head tail) :
    Stability.SeqTailStability Γ Θ σ σ₁ head tail :=
  h.stability

end SeqTailControlSource

/-- Source theorem for producing sequence-tail handoffs. -/
structure SeqTailControlSourceTheorem : Type where
  source :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      Semantics.SeqNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          SeqTailControlSource Γ Θ σ σ₁ head tail

/-- Source for a block-tail local-control handoff. -/
structure BlockTailControlSource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  stability : Stability.BlockTailStability Γ Θ σ σ₁ head tail

namespace BlockTailControlSource

/-- Project the block-tail stability package. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailControlSource Γ Θ σ σ₁ head tail) :
    Stability.BlockTailStability Γ Θ σ σ₁ head tail :=
  h.stability

end BlockTailControlSource

/-- Source theorem for producing block-tail handoffs. -/
structure BlockTailControlSourceTheorem : Type where
  source :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      Semantics.BlockConsNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          BlockTailControlSource Γ Θ σ σ₁ head tail

/-- Source for a selected branch local-control handoff. -/
structure SelectedBranchControlSource
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) (side : Semantics.BranchSide) : Type where
  stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side

namespace SelectedBranchControlSource

/-- Project the selected-branch stability package. -/
def toStability
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch side) :
    Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side :=
  h.stability

end SelectedBranchControlSource

/-- Selected branch source, keeping the selected side explicit. -/
inductive SelectedBranchControlSelection
    (Γ : TypeEnv) (σ : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  | thenSelected
      {Γc : TypeEnv} {σc : State}
      (source : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch
        .thenBranch) :
      SelectedBranchControlSelection Γ σ cond thenBranch elseBranch
  | elseSelected
      {Γc : TypeEnv} {σc : State}
      (source : SelectedBranchControlSource Γ Γc σ σc cond thenBranch elseBranch
        .elseBranch) :
      SelectedBranchControlSelection Γ σ cond thenBranch elseBranch

/-- Source theorem for selected branch handoffs. -/
structure SelectedBranchControlSourceTheorem : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
        SelectedBranchControlSelection Γ σ cond thenBranch elseBranch

/-- Source for entering a while body after a true guard. -/
structure LoopBodyEntryControlSource
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond) (body : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  condition : Boundary.CondBoundary Γ Γc σ cond
  condTrue : Semantics.BigStepCond σ cond true σc
  bodyBoundary : Boundary.StmtBoundary Γc σc body

namespace LoopBodyEntryControlSource

/-- Project the body-entry boundary. -/
def toBodyBoundary
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBodyEntryControlSource Γ Γc σ σc cond body) :
    Boundary.StmtBoundary Γc σc body :=
  h.bodyBoundary

end LoopBodyEntryControlSource

/-- Source theorem for while-body entry after a true guard. -/
structure LoopBodyEntryControlSourceTheorem : Type where
  source :
    ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
        LoopBodyEntryControlSource Γ Γc σ σc cond body

/-- Source for a while normal/continue backedge. -/
structure LoopBackedgeControlSource
    (Γ Γc : TypeEnv) (σ σreentry : State) (cond : CppCond) (body : CppStmt)
    (Reentry : Prop) : Type where
  stability : Stability.WhileBoundaryStability Γ Γc σ cond body
  reentryEq : Stability.WhileBoundaryStability.routePostState stability = σreentry
  reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body)
  certificate : Continuation.ContinuationCertificate Reentry

/-- Source theorem for while normal/continue backedges. -/
structure LoopBackedgeControlSourceTheorem : Type where
  bodyNormal :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .normal σb →
        Σ Reentry : Prop,
          LoopBackedgeControlSource Γ Γc σ σb cond body Reentry
  bodyContinue :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .continueResult σb →
        Σ Reentry : Prop,
          LoopBackedgeControlSource Γ Γc σ σb cond body Reentry

/-- Complete local-control source theorem bundle. -/
structure LocalControlSourceTheorems : Type where
  seq : SeqTailControlSourceTheorem
  blockTail : BlockTailControlSourceTheorem
  branch : SelectedBranchControlSourceTheorem
  whileBody : LoopBodyEntryControlSourceTheorem
  whileBackedge : LoopBackedgeControlSourceTheorem

end Source
end Soundness2
end Cpp3
