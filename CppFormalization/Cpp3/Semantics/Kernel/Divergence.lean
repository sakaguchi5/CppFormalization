import CppFormalization.Cpp3.Semantics.Kernel.Stmt

/-!
# CppFormalization.Cpp3.Semantics.Kernel.Divergence

Divergence kernel for statements and blocks.

The ordinary recursive propagation constructors cover divergence inside selected
subcomputations.  The `whileForever` constructor records the genuinely infinite
case by requiring arbitrarily long finite loop prefixes.
-/

namespace Cpp3
namespace Semantics

/-- A loop body result that re-enters the loop rather than exiting it. -/
def LoopBodyReenters (σ : State) (body : CppStmt) (σ₁ : State) : Prop :=
  BigStepStmt σ body .normal σ₁ ∨
  BigStepStmt σ body .continueResult σ₁

/-- `n` completed true-condition loop iterations from an initial state. -/
inductive WhilePrefix : Nat → State → CppCond → CppStmt → State → Prop where
  | zero
      {σ : State} {cond : CppCond} {body : CppStmt} :
      WhilePrefix 0 σ cond body σ

  | succ
      {n : Nat} {σ σc σb σn : State} {cond : CppCond} {body : CppStmt} :
      BigStepCond σ cond true σc →
      LoopBodyReenters σc body σb →
      WhilePrefix n σb cond body σn →
      WhilePrefix (n + 1) σ cond body σn

mutual

/-- Big-step divergence of a statement. -/
inductive StmtDiv : State → CppStmt → Prop where
  | seqHead
      {σ : State} {head tail : CppStmt} :
      StmtDiv σ head →
      StmtDiv σ (.seq head tail)

  | seqTail
      {σ σ₁ : State} {head tail : CppStmt} :
      BigStepStmt σ head .normal σ₁ →
      StmtDiv σ₁ tail →
      StmtDiv σ (.seq head tail)

  | iteThen
      {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt} :
      BigStepCond σ cond true σc →
      StmtDiv σc thenBranch →
      StmtDiv σ (.ite cond thenBranch elseBranch)

  | iteElse
      {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt} :
      BigStepCond σ cond false σc →
      StmtDiv σc elseBranch →
      StmtDiv σ (.ite cond thenBranch elseBranch)

  | whileBody
      {σ σc : State} {cond : CppCond} {body : CppStmt} :
      BigStepCond σ cond true σc →
      StmtDiv σc body →
      StmtDiv σ (.whileStmt cond body)

  | whileReenter
      {σ σc σb : State} {cond : CppCond} {body : CppStmt} :
      BigStepCond σ cond true σc →
      LoopBodyReenters σc body σb →
      StmtDiv σb (.whileStmt cond body) →
      StmtDiv σ (.whileStmt cond body)

  | whileForever
      {σ : State} {cond : CppCond} {body : CppStmt} :
      (∀ n : Nat, ∃ σn : State, WhilePrefix n σ cond body σn) →
      StmtDiv σ (.whileStmt cond body)

  | block
      {σ : State} {ss : StmtBlock} :
      BlockDiv (pushScope σ) ss →
      StmtDiv σ (.block ss)

/-- Big-step divergence of a statement block. -/
inductive BlockDiv : State → StmtBlock → Prop where
  | consHead
      {σ : State} {head : CppStmt} {tail : StmtBlock} :
      StmtDiv σ head →
      BlockDiv σ (.cons head tail)

  | consTail
      {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock} :
      BigStepStmt σ head .normal σ₁ →
      BlockDiv σ₁ tail →
      BlockDiv σ (.cons head tail)

end

end Semantics
end Cpp3
