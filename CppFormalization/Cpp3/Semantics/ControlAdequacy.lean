import CppFormalization.Cpp3.Semantics.Kernel.Classification
import CppFormalization.Cpp3.Static.FunctionBodyControl

/-!
# CppFormalization.Cpp3.Semantics.ControlAdequacy

Adequacy between finite semantic control results and static control channels.

This is not a new operational semantics.  It records that a finite big-step
result exposes a control channel already represented by the static control
profile.  Soundness uses this to turn the static function-body exclusion of
escaping `break`/`continue` into the runtime fact that only `normal` and
`return` can be successful function-body results.
-/

namespace Cpp3
namespace Semantics

/-- Static control channel exposed by a concrete statement/block result. -/
def controlKindOfResult : CtrlResult → ControlKind
  | .normal => .normalK
  | .breakResult => .breakK
  | .continueResult => .continueK
  | .returnResult _ => .returnK

/-- Runtime statement result accepted at a C++ function-body boundary. -/
def FunctionBodyAcceptableStmtResult : CtrlResult → Prop
  | .normal => True
  | .returnResult _ => True
  | .breakResult => False
  | .continueResult => False

mutual

/-- A finite statement result is reflected by the statement static control profile. -/
theorem stmtControlOfBigStep
    {σ σ₁ : State} {st : CppStmt} {r : CtrlResult}
    (hstep : BigStepStmt σ st r σ₁)
    (hformed : Static.StaticStmtFormed st) :
    Static.StaticStmtControl st (controlKindOfResult r) :=
  match hstep with
  | .skip =>
      Static.StaticStmtControl.skip

  | .exprStmt hExpr => by
      cases hformed with
      | exprStmt hform =>
          exact Static.StaticStmtControl.exprStmt hform

  | .assign hAssign => by
      cases hformed with
      | assign hform =>
          exact Static.StaticStmtControl.assign hform

  | .decl hDecl => by
      cases hformed with
      | decl hform =>
          exact Static.StaticStmtControl.decl hform

  | .jump hJump => by
      cases hJump with
      | breakStmt =>
          exact Static.StaticStmtControl.jumpBreak
      | continueStmt =>
          exact Static.StaticStmtControl.jumpContinue
      | returnVoid =>
          exact Static.StaticStmtControl.jumpReturnVoid
      | returnValue hValue =>
          cases hformed with
          | jump hJumpForm =>
              cases hJumpForm with
              | returnStmt hReturnForm =>
                  cases hReturnForm with
                  | value hValueForm =>
                      exact Static.StaticStmtControl.jumpReturnValue hValueForm

  | .seqNormal hHead hTail => by
      cases hformed with
      | seq hHeadFormed hTailFormed =>
          exact
            Static.StaticStmtControl.seqNormal
              (stmtControlOfBigStep hHead hHeadFormed)
              (stmtControlOfBigStep hTail hTailFormed)

  | .seqBreak hHead => by
      cases hformed with
      | seq hHeadFormed hTailFormed =>
          exact
            Static.StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

  | .seqContinue hHead => by
      cases hformed with
      | seq hHeadFormed hTailFormed =>
          exact
            Static.StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

  | .seqReturn hHead => by
      cases hformed with
      | seq hHeadFormed hTailFormed =>
          exact
            Static.StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

  | .iteThen hCond hBranch => by
      cases hformed with
      | ite hCondFormed hThenFormed hElseFormed =>
          exact
            Static.StaticStmtControl.iteThen
              hCondFormed
              (stmtControlOfBigStep hBranch hThenFormed)
              hElseFormed

  | .iteElse hCond hBranch => by
      cases hformed with
      | ite hCondFormed hThenFormed hElseFormed =>
          exact
            Static.StaticStmtControl.iteElse
              hCondFormed
              hThenFormed
              (stmtControlOfBigStep hBranch hElseFormed)

  | .whileFalse hCond => by
      cases hformed with
      | whileStmt hCondFormed hBodyFormed =>
          exact Static.StaticStmtControl.whileNormal hCondFormed hBodyFormed

  | .whileBodyNormal hCond hBody hLoop =>
      stmtControlOfBigStep hLoop hformed

  | .whileBodyContinue hCond hBody hLoop =>
      stmtControlOfBigStep hLoop hformed

  | .whileBodyBreak hCond hBody => by
      cases hformed with
      | whileStmt hCondFormed hBodyFormed =>
          exact Static.StaticStmtControl.whileNormal hCondFormed hBodyFormed

  | .whileBodyReturn hCond hBody => by
      cases hformed with
      | whileStmt hCondFormed hBodyFormed =>
          exact
            Static.StaticStmtControl.whileReturn
              hCondFormed
              (stmtControlOfBigStep hBody hBodyFormed)

  | .block hBlock hClose => by
      cases hformed with
      | block hBlockFormed =>
          exact
            Static.StaticStmtControl.block
              (blockControlOfBigStep hBlock hBlockFormed)

/-- A finite block result is reflected by the block static control profile. -/
theorem blockControlOfBigStep
    {σ σ₁ : State} {body : StmtBlock} {r : CtrlResult}
    (hstep : BigStepBlock σ body r σ₁)
    (hformed : Static.StaticBlockFormed body) :
    Static.StaticBlockControl body (controlKindOfResult r) :=
  match hstep with
  | .nil =>
      Static.StaticBlockControl.nil

  | .consNormal hHead hTail => by
      cases hformed with
      | cons hHeadFormed hTailFormed =>
          exact
            Static.StaticBlockControl.consNormal
              (stmtControlOfBigStep hHead hHeadFormed)
              (blockControlOfBigStep hTail hTailFormed)

  | .consBreak hHead => by
      cases hformed with
      | cons hHeadFormed hTailFormed =>
          exact
            Static.StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

  | .consContinue hHead => by
      cases hformed with
      | cons hHeadFormed hTailFormed =>
          exact
            Static.StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

  | .consReturn hHead => by
      cases hformed with
      | cons hHeadFormed hTailFormed =>
          exact
            Static.StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControlOfBigStep hHead hHeadFormed)
              hTailFormed

end


/-- The semantic-control adequacy result as a theorem-style wrapper. -/
theorem stmtControl_of_bigStep
    {σ σ₁ : State} {st : CppStmt} {r : CtrlResult}
    (hstep : BigStepStmt σ st r σ₁)
    (hformed : Static.StaticStmtFormed st) :
    Static.StaticStmtControl st (controlKindOfResult r) :=
  stmtControlOfBigStep hstep hformed

/-- The block semantic-control adequacy result as a theorem-style wrapper. -/
theorem blockControl_of_bigStep
    {σ σ₁ : State} {body : StmtBlock} {r : CtrlResult}
    (hstep : BigStepBlock σ body r σ₁)
    (hformed : Static.StaticBlockFormed body) :
    Static.StaticBlockControl body (controlKindOfResult r) :=
  blockControlOfBigStep hstep hformed

/-- Static function-body control excludes unacceptable finite runtime results. -/
theorem acceptableStmtResult_of_staticControl
    {body : CppStmt} {r : CtrlResult}
    (surface : Static.FunctionBodyControlSurface body)
    (hcontrol : Static.StaticStmtControl body (controlKindOfResult r)) :
    FunctionBodyAcceptableStmtResult r := by
  cases r with
  | normal =>
      exact True.intro
  | breakResult =>
      exact False.elim (surface.noEscapingBreak hcontrol)
  | continueResult =>
      exact False.elim (surface.noEscapingContinue hcontrol)
  | returnResult ov =>
      exact True.intro

/-- Static function-body control excludes unacceptable finite big-step results. -/
theorem acceptableStmtResult_of_bigStep
    {σ σ₁ : State} {body : CppStmt} {r : CtrlResult}
    (surface : Static.FunctionBodyControlSurface body)
    (hstep : BigStepStmt σ body r σ₁)
    (hformed : Static.StaticStmtFormed body) :
    FunctionBodyAcceptableStmtResult r :=
  acceptableStmtResult_of_staticControl surface
    (stmtControl_of_bigStep hstep hformed)

end Semantics
end Cpp3
