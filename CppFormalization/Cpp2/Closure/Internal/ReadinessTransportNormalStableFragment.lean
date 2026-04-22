import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalCore
import CppFormalization.Cpp2.Closure.Internal.ResidualTransportStableFragment

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalStableFragment

`ReadinessTransportNormalCore` 全体はまだ bundled debt を含むが、
replay-stable primitive head (`skip / exprStmt / assign`) に限れば、
かなり大きい部分は既に theorem-backed である。

このファイルの役割は、その honest fragment を
core-shape に近い形で明示的に束ねることにある。

重要:
- ここで作るのは full core ではない。
- post environment は replay-stable primitive head では `Γ` に固定される。
- target side も unrestricted ではなく、
  `ReplayStableReadPlace` / `ReplayStableCondExpr` /
  `ReplayTransportableStmt` / `ReplayTransportableBlock`
  に制限する。
-/


/- =========================================================
   1. restricted goal aliases
   ========================================================= -/

abbrev ReplayStablePlaceTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {p : PlaceExpr} {τ : CppType},
    NormalTransportCtx Γ Γ σ σ' head →
    ReplayStableReadPlace p →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    PlaceReadyConcrete Γ σ' p τ

abbrev ReplayStableExprTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {e : ValExpr} {τ : CppType},
    NormalTransportCtx Γ Γ σ σ' head →
    ReplayStableCondExpr e →
    HasValueType Γ e τ →
    ExprReadyConcrete Γ σ e τ →
    ExprReadyConcrete Γ σ' e τ

abbrev ReplayStableStmtTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {t : CppStmt},
    NormalTransportCtx Γ Γ σ σ' head →
    ReplayTransportableStmt t →
    HasTypeStmtCI k Γ t Ω →
    StmtReadyConcrete Γ σ t →
    StmtReadyConcrete Γ σ' t

abbrev ReplayStableBlockTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {ss : StmtBlock},
    NormalTransportCtx Γ Γ σ σ' head →
    ReplayTransportableBlock ss →
    HasTypeBlockCI k Γ ss Ω →
    BlockReadyConcrete Γ σ ss →
    BlockReadyConcrete Γ σ' ss


/- =========================================================
   2. bundled honest stable fragment
   ========================================================= -/

structure ReadinessTransportNormalStableFragment : Type where
  placeTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ReplayStablePrimitiveStmt head →
      ReplayStablePlaceTransportGoal Γ σ σ' head

  exprTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ReplayStablePrimitiveStmt head →
      ReplayStableExprTransportGoal Γ σ σ' head

  stmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ReplayStablePrimitiveStmt head →
      ReplayStableStmtTransportGoal Γ σ σ' head

  blockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ReplayStablePrimitiveStmt head →
      ReplayStableBlockTransportGoal Γ σ σ' head


def readinessTransportNormalStableFragment
    : ReadinessTransportNormalStableFragment := by
  refine
    { placeTransport := ?_
      exprTransport := ?_
      stmtTransport := ?_
      blockTransport := ?_ }

  · intro Γ σ σ' head hhead p τ ctx hpstable _hpTy hpready
    exact
      replay_stable_read_place_ready_after_replay_stable_primitive
        hhead hpstable ctx.hpost hpready ctx.hstep

  · intro Γ σ σ' head hhead e τ ctx hc _hvty heready
    exact
      replay_stable_cond_expr_ready_after_replay_stable_primitive
        hhead hc ctx.hpost heready ctx.hstep

  · intro Γ σ σ' head hhead k Ω t ctx htarget _hty hready
    exact
      replay_transportable_stmt_ready_after_replay_stable_primitive_head
        hhead htarget ctx.hpost hready ctx.hstep

  · intro Γ σ σ' head hhead k Ω ss ctx hblock _hty hready
    exact
      replay_transportable_block_ready_after_replay_stable_primitive_head
        hhead hblock ctx.hpost hready ctx.hstep


/- =========================================================
   3. thin theorem corollaries
   ========================================================= -/

theorem replay_stable_place_ready_transport_of_normal_ctx
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayStablePlaceTransportGoal Γ σ σ' head :=
  readinessTransportNormalStableFragment.placeTransport

theorem replay_stable_expr_ready_transport_of_normal_ctx
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayStableExprTransportGoal Γ σ σ' head :=
  readinessTransportNormalStableFragment.exprTransport

theorem replay_stable_stmt_ready_transport_of_normal_ctx
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayStableStmtTransportGoal Γ σ σ' head :=
  readinessTransportNormalStableFragment.stmtTransport

theorem replay_stable_block_ready_transport_of_normal_ctx
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayStableBlockTransportGoal Γ σ σ' head :=
  readinessTransportNormalStableFragment.blockTransport

end Cpp
