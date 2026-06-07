import CppFormalization.Cpp3.Semantics.Primitive

/-!
# CppFormalization.Cpp3.Semantics.Stmt

Concrete big-step statement and block semantics.

This is intentionally only the operational routing layer.  It says how `seq`,
`if`, `while`, and block bodies route runtime control results; it does not claim
that the selected tail/branch/backedge boundary is safe.  Boundary and Stability
will provide those facts later.
-/

namespace Cpp3
namespace Semantics

mutual

/-- Big-step execution of a statement to a control result and post-state. -/
inductive BigStepStmt : State → CppStmt → CtrlResult → State → Prop where
  | skip
      {σ : State} :
      BigStepStmt σ .skip .normal σ

  | exprStmt
      {σ σ₁ : State} {e : CppExprStmt} :
      BigStepExprStmt σ e σ₁ →
      BigStepStmt σ (.exprStmt e) .normal σ₁

  | assign
      {σ σ₁ : State} {a : CppAssign} :
      BigStepAssign σ a σ₁ →
      BigStepStmt σ (.assign a) .normal σ₁

  | decl
      {σ σ₁ : State} {d : CppDecl} :
      BigStepDecl σ d σ₁ →
      BigStepStmt σ (.decl d) .normal σ₁

  | jump
      {σ σ₁ : State} {j : CppJump} {r : CtrlResult} :
      BigStepJump σ j r σ₁ →
      BigStepStmt σ (.jump j) r σ₁

  | seqNormal
      {σ σ₁ σ₂ : State} {head tail : CppStmt} {r : CtrlResult} :
      BigStepStmt σ head .normal σ₁ →
      BigStepStmt σ₁ tail r σ₂ →
      BigStepStmt σ (.seq head tail) r σ₂

  | seqBreak
      {σ σ₁ : State} {head tail : CppStmt} :
      BigStepStmt σ head .breakResult σ₁ →
      BigStepStmt σ (.seq head tail) .breakResult σ₁

  | seqContinue
      {σ σ₁ : State} {head tail : CppStmt} :
      BigStepStmt σ head .continueResult σ₁ →
      BigStepStmt σ (.seq head tail) .continueResult σ₁

  | seqReturn
      {σ σ₁ : State} {head tail : CppStmt} {ov : Option Value} :
      BigStepStmt σ head (.returnResult ov) σ₁ →
      BigStepStmt σ (.seq head tail) (.returnResult ov) σ₁

  | iteThen
      {σ σc σ₁ : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
      {r : CtrlResult} :
      BigStepCond σ cond true σc →
      BigStepStmt σc thenBranch r σ₁ →
      BigStepStmt σ (.ite cond thenBranch elseBranch) r σ₁

  | iteElse
      {σ σc σ₁ : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
      {r : CtrlResult} :
      BigStepCond σ cond false σc →
      BigStepStmt σc elseBranch r σ₁ →
      BigStepStmt σ (.ite cond thenBranch elseBranch) r σ₁

  | whileFalse
      {σ σc : State} {cond : CppCond} {body : CppStmt} :
      BigStepCond σ cond false σc →
      BigStepStmt σ (.whileStmt cond body) .normal σc

  | whileBodyNormal
      {σ σc σb σ₁ : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult} :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .normal σb →
      BigStepStmt σb (.whileStmt cond body) r σ₁ →
      BigStepStmt σ (.whileStmt cond body) r σ₁

  | whileBodyContinue
      {σ σc σb σ₁ : State} {cond : CppCond} {body : CppStmt} {r : CtrlResult} :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .continueResult σb →
      BigStepStmt σb (.whileStmt cond body) r σ₁ →
      BigStepStmt σ (.whileStmt cond body) r σ₁

  | whileBodyBreak
      {σ σc σb : State} {cond : CppCond} {body : CppStmt} :
      BigStepCond σ cond true σc →
      BigStepStmt σc body .breakResult σb →
      BigStepStmt σ (.whileStmt cond body) .normal σb

  | whileBodyReturn
      {σ σc σb : State} {cond : CppCond} {body : CppStmt} {ov : Option Value} :
      BigStepCond σ cond true σc →
      BigStepStmt σc body (.returnResult ov) σb →
      BigStepStmt σ (.whileStmt cond body) (.returnResult ov) σb

  | block
      {σ σbody σ₁ : State} {ss : StmtBlock} {r : CtrlResult} :
      BigStepBlock (pushScope σ) ss r σbody →
      popScope? σbody = some σ₁ →
      BigStepStmt σ (.block ss) r σ₁

/-- Big-step execution of a statement block to a control result and post-state. -/
inductive BigStepBlock : State → StmtBlock → CtrlResult → State → Prop where
  | nil
      {σ : State} :
      BigStepBlock σ .nil .normal σ

  | consNormal
      {σ σ₁ σ₂ : State} {head : CppStmt} {tail : StmtBlock} {r : CtrlResult} :
      BigStepStmt σ head .normal σ₁ →
      BigStepBlock σ₁ tail r σ₂ →
      BigStepBlock σ (.cons head tail) r σ₂

  | consBreak
      {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock} :
      BigStepStmt σ head .breakResult σ₁ →
      BigStepBlock σ (.cons head tail) .breakResult σ₁

  | consContinue
      {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock} :
      BigStepStmt σ head .continueResult σ₁ →
      BigStepBlock σ (.cons head tail) .continueResult σ₁

  | consReturn
      {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock} {ov : Option Value} :
      BigStepStmt σ head (.returnResult ov) σ₁ →
      BigStepBlock σ (.cons head tail) (.returnResult ov) σ₁

end

end Semantics
end Cpp3
