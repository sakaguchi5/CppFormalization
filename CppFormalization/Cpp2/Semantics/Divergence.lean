import CppFormalization.Cpp2.Semantics.Stmt

/-!
Divergence and the residual stuck notion.
-/

namespace Cpp

class NoExprDivergence : Prop where
  no_div : True

def LoopBodyAdvances (σ : State) (body : CppStmt) (σ' : State) : Prop :=
  BigStepStmt σ body .normal σ' ∨
  BigStepStmt σ body .continueResult σ'

inductive WhilePrefix : Nat → State → ValExpr → CppStmt → State → Prop where
  | zero {σ : State} {c : ValExpr} {body : CppStmt} :
      WhilePrefix 0 σ c body σ
  | succ {n : Nat} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      LoopBodyAdvances σ body σ₁ →
      WhilePrefix n σ₁ c body σ₂ →
      WhilePrefix (n + 1) σ c body σ₂

mutual

inductive BigStepStmtDiv : State → CppStmt → Prop where
  | seqLeft {σ : State} {s t : CppStmt} :
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.seq s t)

  | seqRight {σ σ₁ : State} {s t : CppStmt} :
      BigStepStmt σ s .normal σ₁ →
      BigStepStmtDiv σ₁ t →
      BigStepStmtDiv σ (.seq s t)

  | iteTrue {σ : State} {c : ValExpr} {s t : CppStmt} :
      BigStepValue σ c (.bool true) →
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.ite c s t)

  | iteFalse {σ : State} {c : ValExpr} {s t : CppStmt} :
      BigStepValue σ c (.bool false) →
      BigStepStmtDiv σ t →
      BigStepStmtDiv σ (.ite c s t)

  | whileBody {σ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      BigStepStmtDiv σ body →
      BigStepStmtDiv σ (.whileStmt c body)

  | whileIter {σ σ₁ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      LoopBodyAdvances σ body σ₁ →
      BigStepStmtDiv σ₁ (.whileStmt c body) →
      BigStepStmtDiv σ (.whileStmt c body)

  | whileForever {σ : State} {c : ValExpr} {body : CppStmt} :
      (∀ n : Nat, ∃ σn : State, WhilePrefix n σ c body σn) →
      BigStepStmtDiv σ (.whileStmt c body)

  | block {σ σ₁ : State} {ss : StmtBlock} :
      OpenScope σ σ₁ →
      BigStepBlockDiv σ₁ ss →
      BigStepStmtDiv σ (.block ss)

inductive BigStepBlockDiv : State → StmtBlock → Prop where
  | consHere {σ : State} {s : CppStmt} {ss : StmtBlock} :
      BigStepStmtDiv σ s →
      BigStepBlockDiv σ (.cons s ss)

  | consTail {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock} :
      BigStepStmt σ s .normal σ₁ →
      BigStepBlockDiv σ₁ ss →
      BigStepBlockDiv σ (.cons s ss)

end


def UnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ BigStepStmtTerminates σ st ∧ ¬ BigStepStmtDiv σ st

end Cpp
