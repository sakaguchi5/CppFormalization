import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
# Closure.Internal.ReadinessReplayPrimitive

while / seq / block の replay を進めるとき、primitive case に本当に必要なのは
「normal 実行後に同じ文をもう一度 ready と見なせるか」である。

ただし、この replay 性質は primitive 全体ではなく、環境を保存する primitive に限る。
`declareObj` / `declareRef` は top-scope freshness を消費し、post-state では同じ宣言文を
そのまま再実行可能とは限らないので、replay-stable base からは外す。

このファイルでは:
- replay-stable primitive を `skip / exprStmt / assign` に限定する
- `skip / exprStmt` は theorem で閉じる
- `assign` の replay は `AssignTransportKernel` へ束ねた primitive obligations を使って
  statement replay を theorem として組み立てる
-/

/--
Primitive normal 文のうち、post-state でも「同じ文」が再び ready であることを
期待できる replay-stable base.

現段階では `skip / exprStmt / assign` のみを含める。
宣言文は freshness を消費するので含めない。
-/
def ReplayStablePrimitiveStmt : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => False
  | .declareRef _ _ _ => False
  | .breakStmt => False
  | .continueStmt => False
  | .returnStmt _ => False
  | .seq _ _ => False
  | .ite _ _ _ => False
  | .whileStmt _ _ => False
  | .block _ => False


/- =========================================================
   1. zero-update primitives
   ========================================================= -/

theorem skip_stmt_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State} :
    StmtReadyConcrete Γ σ .skip →
    BigStepStmt σ .skip .normal σ' →
    StmtReadyConcrete Γ σ' .skip := by
  intro hready hstep
  cases hstep
  simpa using hready


theorem exprStmt_stmt_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State} {e : ValExpr} :
    StmtReadyConcrete Γ σ (.exprStmt e) →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    StmtReadyConcrete Γ σ' (.exprStmt e) := by
  intro hready hstep
  cases hstep
  simpa using hready


/- =========================================================
   2. assign replay via bundled transport kernel
   ========================================================= -/

theorem assign_stmt_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} :
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.assign p e) →
    BigStepStmt σ (.assign p e) .normal σ' →
    StmtReadyConcrete Γ σ' (.assign p e) := by
  intro hσ' hready hstep
  cases hready with
  | assign hpty hpready hvty heready =>
      refine StmtReadyConcrete.assign hpty ?_ hvty ?_
      · exact assign_place_ready_replay_concrete hσ' hpready hstep
      · exact assign_expr_ready_replay_concrete hvty hσ' heready hstep


/- =========================================================
   3. bundled replay theorem for the stable primitive base
   ========================================================= -/

theorem replay_stable_primitive_stmt_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ st .normal σ' →
    StmtReadyConcrete Γ σ' st := by
  intro hstable hσ' hready hstep
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable
  case skip =>
    exact skip_stmt_ready_replay_concrete hready hstep
  case exprStmt e =>
    exact exprStmt_stmt_ready_replay_concrete hready hstep
  case assign p e =>
    exact assign_stmt_ready_replay_concrete hσ' hready hstep


theorem replay_stable_primitive_stmt_env_preserving
    {Γ Δ : TypeEnv} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    HasTypeStmtCI .normalK Γ st Δ →
    Δ = Γ := by
  intro hstable hty
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable
  case skip =>
    cases hty
    rfl
  case exprStmt e =>
    cases hty
    rfl
  case assign p e =>
    cases hty
    rfl

end Cpp
