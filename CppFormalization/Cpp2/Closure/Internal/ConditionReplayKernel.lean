import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Closure.Internal.ConditionReplayKernel

while 条件の replay で本当に必要なのは、
「条件式の truth value を保つ」ことではなく、
「post-state でも同じ条件式を安全に再評価できる」ことである。

このファイルでは、それを full `ValExpr` ではなく、
当面の while 本線に必要な最小 fragment に対して与える。

設計方針:
- `PtrValueReadyAt` / aliasing kernel が未整備なので `deref` は除外する
- `load` / `addrOf` は replay-stable read place に限る
- theorem の中心は `HasValueType` ではなく `ExprReadyConcrete` witness の輸送
- `skip` / `exprStmt` は theorem、`assign` の核は `AssignTransportKernel` へ移した
-/


/--
while 条件を構成する値式のうち、replay kernel の対象に含める最小 fragment。

注意:
- ここで「condition」と呼んでいるが、`lt` / `eq` の部分式として int 式も含む。
- `load` / `addrOf` は replay-stable read place に限定する。
- `deref` を含む条件は、place 側の kernel が未整備なので当面除外する。
-/
inductive ReplayStableCondExpr : ValExpr → Prop where
  | litBool {b : Bool} :
      ReplayStableCondExpr (.litBool b)
  | litInt {n : Int} :
      ReplayStableCondExpr (.litInt n)
  | load {p : PlaceExpr} :
      ReplayStableReadPlace p →
      ReplayStableCondExpr (.load p)
  | addrOf {p : PlaceExpr} :
      ReplayStableReadPlace p →
      ReplayStableCondExpr (.addrOf p)
  | add {e₁ e₂ : ValExpr} :
      ReplayStableCondExpr e₁ →
      ReplayStableCondExpr e₂ →
      ReplayStableCondExpr (.add e₁ e₂)
  | sub {e₁ e₂ : ValExpr} :
      ReplayStableCondExpr e₁ →
      ReplayStableCondExpr e₂ →
      ReplayStableCondExpr (.sub e₁ e₂)
  | mul {e₁ e₂ : ValExpr} :
      ReplayStableCondExpr e₁ →
      ReplayStableCondExpr e₂ →
      ReplayStableCondExpr (.mul e₁ e₂)
  | eq {e₁ e₂ : ValExpr} :
      ReplayStableCondExpr e₁ →
      ReplayStableCondExpr e₂ →
      ReplayStableCondExpr (.eq e₁ e₂)
  | lt {e₁ e₂ : ValExpr} :
      ReplayStableCondExpr e₁ →
      ReplayStableCondExpr e₂ →
      ReplayStableCondExpr (.lt e₁ e₂)
  | not {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayStableCondExpr (.not e)


/- =========================================================
   1. zero-update primitives
   ========================================================= -/

theorem replay_stable_read_place_ready_after_skip
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ .skip .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro _ hready hstep
  cases hstep
  simpa using hready


theorem replay_stable_read_place_ready_after_exprStmt
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro _ hready hstep
  cases hstep
  simpa using hready


theorem replay_stable_cond_expr_ready_after_skip
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {τ : CppType} :
    ReplayStableCondExpr c →
    ExprReadyConcrete Γ σ c τ →
    BigStepStmt σ .skip .normal σ' →
    ExprReadyConcrete Γ σ' c τ := by
  intro _ hready hstep
  cases hstep
  simpa using hready


theorem replay_stable_cond_expr_ready_after_exprStmt
    {Γ : TypeEnv} {σ σ' : State} {c e : ValExpr} {τ : CppType} :
    ReplayStableCondExpr c →
    ExprReadyConcrete Γ σ c τ →
    BigStepStmt σ (.exprStmt e) .normal σ' →
    ExprReadyConcrete Γ σ' c τ := by
  intro _ hready hstep
  cases hstep
  simpa using hready


/- =========================================================
   2. assign 後の condition-ready replay
   ========================================================= -/

theorem replay_stable_cond_expr_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {τ : CppType} {p : PlaceExpr} {e : ValExpr} :
    ReplayStableCondExpr c →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ c τ →
    BigStepStmt σ (.assign p e) .normal σ' →
    ExprReadyConcrete Γ σ' c τ := by
  intro hc hσ' hready hstep
  induction hc generalizing τ σ σ' p e with
  | litBool =>
      cases hready
      exact ExprReadyConcrete.litBool
  | litInt =>
      cases hready
      exact ExprReadyConcrete.litInt
  | load hstableP =>
      cases hready with
      | load hpready hread =>
          exact ExprReadyConcrete.load
            (replay_stable_read_place_ready_after_assign hstableP hσ' hpready hstep)
            (replay_stable_load_readable_after_assign hstableP hσ' hread hstep)
  | addrOf hstableP =>
      cases hready with
      | addrOf hpready =>
          exact ExprReadyConcrete.addrOf
            (replay_stable_read_place_ready_after_assign hstableP hσ' hpready hstep)
  | add hc1 hc2 ih1 ih2 =>
      cases hready with
      | add h1 h2 =>
          exact ExprReadyConcrete.add
            (ih1 hσ' h1 hstep)
            (ih2 hσ' h2 hstep)
  | sub hc1 hc2 ih1 ih2 =>
      cases hready with
      | sub h1 h2 =>
          exact ExprReadyConcrete.sub
            (ih1 hσ' h1 hstep)
            (ih2 hσ' h2 hstep)
  | mul hc1 hc2 ih1 ih2 =>
      cases hready with
      | mul h1 h2 =>
          exact ExprReadyConcrete.mul
            (ih1 hσ' h1 hstep)
            (ih2 hσ' h2 hstep)
  | eq hc1 hc2 ih1 ih2 =>
      cases hready with
      | eq h1 h2 =>
          exact ExprReadyConcrete.eq
            (ih1 hσ' h1 hstep)
            (ih2 hσ' h2 hstep)
  | lt hc1 hc2 ih1 ih2 =>
      cases hready with
      | lt h1 h2 =>
          exact ExprReadyConcrete.lt
            (ih1 hσ' h1 hstep)
            (ih2 hσ' h2 hstep)
  | not hc ih =>
      cases hready with
      | not h =>
          exact ExprReadyConcrete.not (ih hσ' h hstep)


/- =========================================================
   3. replay-stable primitive 文に束ねる
   ========================================================= -/

theorem replay_stable_cond_expr_ready_after_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {τ : CppType} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ReplayStableCondExpr c →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ c τ →
    BigStepStmt σ st .normal σ' →
    ExprReadyConcrete Γ σ' c τ := by
  intro hstable hc hσ' hready hstep
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable
  case skip =>
    exact replay_stable_cond_expr_ready_after_skip hc hready hstep
  case exprStmt e =>
    exact replay_stable_cond_expr_ready_after_exprStmt hc hready hstep
  case assign p e =>
    exact replay_stable_cond_expr_ready_after_assign hc hσ' hready hstep

end Cpp
