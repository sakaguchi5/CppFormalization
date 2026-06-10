import CppFormalization.Cpp3.Semantics.Kernel.Classification
import CppFormalization.Cpp3.Static.ControlProfile
import CppFormalization.Cpp3.Static.FunctionBodyControl
/-!
# CppFormalization.Cpp3.Static.ControlAdequacy

Static/control adequacy for the executable statement kernel.

The key direction needed by function-body soundness is not that static control
predicts a concrete execution, but the converse safety fact: if a well-formed
statement or block actually produces a finite control result, then that result
is one of the statically visible control channels.

The `Static*Formed` premise is essential for C++: an abrupt sequence/block head
short-circuits the tail at runtime, so the big-step derivation alone does not
inspect whether the skipped tail is statically admitted.
-/

namespace Cpp3
namespace Static

/-- The static control channel corresponding to a runtime control result. -/
def controlKindOfCtrlResult : CtrlResult → ControlKind
  | .normal => .normalK
  | .breakResult => .breakK
  | .continueResult => .continueK
  | .returnResult _ => .returnK

mutual

/-- A finite statement result is visible in the static statement-control profile. -/
theorem stmtControl_of_bigStepStmt_result
    {σ σ₁ : State} {st : CppStmt} {r : CtrlResult} :
    StaticStmtFormed st →
    Semantics.BigStepStmt σ st r σ₁ →
    StaticStmtControl st (controlKindOfCtrlResult r)
  | formed, Semantics.BigStepStmt.skip =>
      StaticStmtControl.skip

  | formed, Semantics.BigStepStmt.exprStmt exprStep => by
      cases formed with
      | exprStmt exprFormed =>
          exact StaticStmtControl.exprStmt exprFormed

  | formed, Semantics.BigStepStmt.assign assignStep => by
      cases formed with
      | assign assignFormed =>
          exact StaticStmtControl.assign assignFormed

  | formed, Semantics.BigStepStmt.decl declStep => by
      cases formed with
      | decl declFormed =>
          exact StaticStmtControl.decl declFormed

  | formed, Semantics.BigStepStmt.jump jumpStep => by
      cases jumpStep with
      | breakStmt =>
          exact StaticStmtControl.jumpBreak
      | continueStmt =>
          exact StaticStmtControl.jumpContinue
      | returnVoid =>
          exact StaticStmtControl.jumpReturnVoid
      | returnValue valueStep =>
          cases formed with
          | jump jumpFormed =>
              cases jumpFormed with
              | returnStmt returnFormed =>
                  cases returnFormed with
                  | value valueFormed =>
                      exact StaticStmtControl.jumpReturnValue valueFormed

  | formed, Semantics.BigStepStmt.seqNormal headStep tailStep => by
      cases formed with
      | seq headFormed tailFormed =>
          exact
            StaticStmtControl.seqNormal
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              (stmtControl_of_bigStepStmt_result tailFormed tailStep)

  | formed, Semantics.BigStepStmt.seqBreak headStep => by
      cases formed with
      | seq headFormed tailFormed =>
          exact
            StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

  | formed, Semantics.BigStepStmt.seqContinue headStep => by
      cases formed with
      | seq headFormed tailFormed =>
          exact
            StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

  | formed, Semantics.BigStepStmt.seqReturn headStep => by
      cases formed with
      | seq headFormed tailFormed =>
          exact
            StaticStmtControl.seqAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

  | formed, Semantics.BigStepStmt.iteThen condStep branchStep => by
      cases formed with
      | ite condFormed thenFormed elseFormed =>
          exact
            StaticStmtControl.iteThen
              condFormed
              (stmtControl_of_bigStepStmt_result thenFormed branchStep)
              elseFormed

  | formed, Semantics.BigStepStmt.iteElse condStep branchStep => by
      cases formed with
      | ite condFormed thenFormed elseFormed =>
          exact
            StaticStmtControl.iteElse
              condFormed
              thenFormed
              (stmtControl_of_bigStepStmt_result elseFormed branchStep)

  | formed, Semantics.BigStepStmt.whileFalse condStep => by
      cases formed with
      | whileStmt condFormed bodyFormed =>
          exact StaticStmtControl.whileNormal condFormed bodyFormed

  | formed, Semantics.BigStepStmt.whileBodyNormal condStep bodyStep loopStep =>
      stmtControl_of_bigStepStmt_result formed loopStep

  | formed, Semantics.BigStepStmt.whileBodyContinue condStep bodyStep loopStep =>
      stmtControl_of_bigStepStmt_result formed loopStep

  | formed, Semantics.BigStepStmt.whileBodyBreak condStep bodyStep => by
      cases formed with
      | whileStmt condFormed bodyFormed =>
          exact StaticStmtControl.whileNormal condFormed bodyFormed

  | formed, Semantics.BigStepStmt.whileBodyReturn condStep bodyStep => by
      cases formed with
      | whileStmt condFormed bodyFormed =>
          exact
            StaticStmtControl.whileReturn
              condFormed
              (stmtControl_of_bigStepStmt_result bodyFormed bodyStep)

  | formed, Semantics.BigStepStmt.block bodyStep closeStep => by
      cases formed with
      | block blockFormed =>
          exact
            StaticStmtControl.block
              (blockControl_of_bigStepBlock_result blockFormed bodyStep)


/-- A finite block result is visible in the static block-control profile. -/
theorem blockControl_of_bigStepBlock_result
    {σ σ₁ : State} {body : StmtBlock} {r : CtrlResult} :
    StaticBlockFormed body →
    Semantics.BigStepBlock σ body r σ₁ →
    StaticBlockControl body (controlKindOfCtrlResult r)
  | formed, Semantics.BigStepBlock.nil =>
      StaticBlockControl.nil

  | formed, Semantics.BigStepBlock.consNormal headStep tailStep => by
      cases formed with
      | cons headFormed tailFormed =>
          exact
            StaticBlockControl.consNormal
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              (blockControl_of_bigStepBlock_result tailFormed tailStep)

  | formed, Semantics.BigStepBlock.consBreak headStep => by
      cases formed with
      | cons headFormed tailFormed =>
          exact
            StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

  | formed, Semantics.BigStepBlock.consContinue headStep => by
      cases formed with
      | cons headFormed tailFormed =>
          exact
            StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

  | formed, Semantics.BigStepBlock.consReturn headStep => by
      cases formed with
      | cons headFormed tailFormed =>
          exact
            StaticBlockControl.consAbrupt
              (by trivial)
              (stmtControl_of_bigStepStmt_result headFormed headStep)
              tailFormed

end

/-- A function-body control surface rules out finite top-level `break`. -/
theorem no_breakResult_of_functionBodyControl
    {σ σ₁ : State} {body : CppStmt}
    (control : FunctionBodyControlSurface body)
    (formed : StaticStmtFormed body)
    (step : Semantics.BigStepStmt σ body .breakResult σ₁) :
    False := by
  exact control.noEscapingBreak
    (stmtControl_of_bigStepStmt_result formed step)

/-- A function-body control surface rules out finite top-level `continue`. -/
theorem no_continueResult_of_functionBodyControl
    {σ σ₁ : State} {body : CppStmt}
    (control : FunctionBodyControlSurface body)
    (formed : StaticStmtFormed body)
    (step : Semantics.BigStepStmt σ body .continueResult σ₁) :
    False := by
  exact control.noEscapingContinue
    (stmtControl_of_bigStepStmt_result formed step)

end Static
end Cpp3
