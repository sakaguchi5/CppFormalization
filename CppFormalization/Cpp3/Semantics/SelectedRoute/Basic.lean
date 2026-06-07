import CppFormalization.Cpp3.Semantics.Kernel.Stmt

/-!
# CppFormalization.Cpp3.Semantics.SelectedRoute.Basic

Thin selected-runtime-route vocabulary.

This layer sits above `Semantics.Kernel`: it observes which operational route was
selected and records the relevant post-state.  It still does not assert that a
tail, selected branch, loop backedge, or opened block boundary is safe.  Later
Boundary/Stability/Continuation layers should consume these routes and attach
those obligations.
-/

namespace Cpp3
namespace Semantics

/-- Route produced by a statement head that finishes normally and exposes a tail. -/
structure SeqNormalRoute
    (σ σ₁ : State) (head tail : CppStmt) : Type where
  headNormal : BigStepStmt σ head .normal σ₁

/-- Route produced by a block head that finishes normally and exposes a block tail. -/
structure BlockConsNormalRoute
    (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  headNormal : BigStepStmt σ head .normal σ₁

/-- Runtime side selected by a condition. -/
inductive BranchSide where
  | thenBranch
  | elseBranch
  deriving DecidableEq, Repr

/-- Condition route selecting the branch of an `if` statement. -/
inductive SelectedBranchRoute
    (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : BranchSide → Type where
  | thenRoute :
      BigStepCond σ cond true σc →
      SelectedBranchRoute σ σc cond thenBranch elseBranch .thenBranch

  | elseRoute :
      BigStepCond σ cond false σc →
      SelectedBranchRoute σ σc cond thenBranch elseBranch .elseBranch

/-- One-step runtime route at a while-loop boundary. -/
inductive WhileBoundaryRoute
    (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  | exit
      (σc : State) :
      BigStepCond σ cond false σc →
      WhileBoundaryRoute σ cond body

  | bodyNormal
      (σc σb : State) :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .normal σb →
      WhileBoundaryRoute σ cond body

  | bodyContinue
      (σc σb : State) :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .continueResult σb →
      WhileBoundaryRoute σ cond body

  | bodyBreak
      (σc σb : State) :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .breakResult σb →
      WhileBoundaryRoute σ cond body

  | bodyReturn
      (σc σb : State) (ov : Option Value) :
      BigStepCond σ cond true σc →
      BigStepStmt σc body (.returnResult ov) σb →
      WhileBoundaryRoute σ cond body

namespace WhileBoundaryRoute

/-- State reached immediately after condition evaluation. -/
def conditionPostState
    {σ : State} {cond : CppCond} {body : CppStmt} :
    WhileBoundaryRoute σ cond body → State
  | exit σc _ => σc
  | bodyNormal σc _ _ _ => σc
  | bodyContinue σc _ _ _ => σc
  | bodyBreak σc _ _ _ => σc
  | bodyReturn σc _ _ _ _ => σc

/-- State reached after the one-step while boundary route. -/
def routePostState
    {σ : State} {cond : CppCond} {body : CppStmt} :
    WhileBoundaryRoute σ cond body → State
  | exit σc _ => σc
  | bodyNormal _ σb _ _ => σb
  | bodyContinue _ σb _ _ => σb
  | bodyBreak _ σb _ _ => σb
  | bodyReturn _ σb _ _ _ => σb

end WhileBoundaryRoute

/-- Route for entering an opened block body. -/
structure OpenedBlockRoute
    (σ σopened : State) (body : StmtBlock) : Type where
  opened : σopened = pushScope σ

end Semantics
end Cpp3
