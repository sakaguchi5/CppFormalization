import CppFormalization.Cpp2.Closure.Foundation.Readiness

namespace Cpp

/-!
# Closure.Foundation.ReadinessInversions

`StmtReadyConcrete` / `BlockReadyConcrete` の純粋な inversion library.

役割:
- transport theorem から readiness の constructor 分解を切り離す。
- seq / ite / while / block / block-body の readiness 射影を、
  foundation 側の再利用可能補題としてまとめる。

重要:
- ここに置くのは pure inversion のみ。
- preservation や closure transport 自体は持ち込まない。
-/

@[simp] theorem stmtReadyConcrete_seq_left
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | seq hs ht =>
      exact hs

@[simp] theorem stmtReadyConcrete_seq_right
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | seq hs ht =>
      exact ht

@[simp] theorem stmtReadyConcrete_ite_cond
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | ite _ hc hs ht =>
      exact hc

@[simp] theorem stmtReadyConcrete_ite_then
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | ite _ hc hs ht =>
      exact hs

@[simp] theorem stmtReadyConcrete_ite_else
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | ite _ hc hs ht =>
      exact ht

@[simp] theorem stmtReadyConcrete_while_cond
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt _ hc hbody =>
      exact hc

@[simp] theorem stmtReadyConcrete_while_body
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    StmtReadyConcrete Γ σ body := by
  intro h
  cases h with
  | whileStmt _ hc hbody =>
      exact hbody

@[simp] theorem stmtReadyConcrete_block_body
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    StmtReadyConcrete Γ σ (.block ss) →
    BlockReadyConcrete (pushTypeScope Γ) (pushScope σ) ss := by
  intro h
  cases h with
  | block hss =>
      exact hss

@[simp] theorem blockReadyConcrete_cons_head
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | cons hs hss =>
      exact hs

@[simp] theorem blockReadyConcrete_cons_tail
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) →
    BlockReadyConcrete Γ σ ss := by
  intro h
  cases h with
  | cons hs hss =>
      exact hss

end Cpp
