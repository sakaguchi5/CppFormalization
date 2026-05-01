import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalStableFragment

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalEnvPreserving

Theorem-backed transport layer for env-preserving normal heads.

At this stage of the development:
- `ReadinessTransportNormalCore` is the single choke point for the remaining
  bundled tail-ready debt.
- the replay-stable primitive fragment is already theorem-backed.
- those heads are exactly the normal heads that preserve the ambient type
  environment (`skip / exprStmt / assign`).

This file packages that theorem-backed fragment behind an
`EnvPreservingNormalHead` alias and thin wrappers, so the future proof of the
full core can case-split on the head class without talking directly about the
stable fragment every time.
-/


/- =========================================================
   1. env-preserving head class
   ========================================================= -/

/--
Current theorem-backed env-preserving normal heads.

For now this is definitionally the replay-stable primitive head fragment.
That is not an arbitrary naming choice: in the current development these are
exactly the heads for which we already know both
- post environment stays `Γ`
- readiness transport is theorem-backed on the stable target fragment.
-/
abbrev EnvPreservingNormalHead : CppStmt → Prop :=
  ReplayStablePrimitiveStmt

theorem env_preserving_normal_head_same_env
    {Γ Δ : TypeEnv} {head : CppStmt} :
    EnvPreservingNormalHead head →
    HasTypeStmtCI .normalK Γ head Δ →
    Δ = Γ := by
  intro hhead hty
  exact replay_stable_primitive_stmt_env_preserving hhead hty

theorem env_preserving_normal_ctx_same_env
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvPreservingNormalHead head →
    NormalTransportCtx Γ Δ σ σ' head →
    Δ = Γ := by
  intro hhead hctx
  exact env_preserving_normal_head_same_env hhead hctx.hty


/- =========================================================
   2. theorem-backed transport wrappers
   ========================================================= -/

theorem env_preserving_place_ready_transport_of_normal
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvPreservingNormalHead head →
    ReplayStablePlaceTransportGoal Γ σ σ' head := by
  intro hhead
  exact replay_stable_place_ready_transport_of_normal_ctx hhead

theorem env_preserving_expr_ready_transport_of_normal
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvPreservingNormalHead head →
    ReplayStableExprTransportGoal Γ σ σ' head := by
  intro hhead
  exact replay_stable_expr_ready_transport_of_normal_ctx hhead

theorem env_preserving_stmt_ready_transport_of_normal
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvPreservingNormalHead head →
    ReplayStableStmtTransportGoal Γ σ σ' head := by
  intro hhead
  exact replay_stable_stmt_ready_transport_of_normal_ctx hhead

theorem env_preserving_block_ready_transport_of_normal
    {Γ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvPreservingNormalHead head →
    ReplayStableBlockTransportGoal Γ σ σ' head := by
  intro hhead
  exact replay_stable_block_ready_transport_of_normal_ctx hhead


/- =========================================================
   3. bundled theorem-backed env-preserving fragment
   ========================================================= -/

structure ReadinessTransportNormalEnvPreservingFragment : Type where
  sameEnv :
    ∀ {Γ Δ : TypeEnv} {head : CppStmt},
      EnvPreservingNormalHead head →
      HasTypeStmtCI .normalK Γ head Δ →
      Δ = Γ

  placeTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      EnvPreservingNormalHead head →
      ReplayStablePlaceTransportGoal Γ σ σ' head

  exprTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      EnvPreservingNormalHead head →
      ReplayStableExprTransportGoal Γ σ σ' head

  stmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      EnvPreservingNormalHead head →
      ReplayStableStmtTransportGoal Γ σ σ' head

  blockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {head : CppStmt},
      EnvPreservingNormalHead head →
      ReplayStableBlockTransportGoal Γ σ σ' head

def readinessTransportNormalEnvPreservingFragment
    : ReadinessTransportNormalEnvPreservingFragment := by
  refine
    { sameEnv := ?_
      placeTransport := ?_
      exprTransport := ?_
      stmtTransport := ?_
      blockTransport := ?_ }
  · intro Γ Δ head hhead hty
    exact env_preserving_normal_head_same_env hhead hty
  · intro Γ σ σ' head hhead
    exact env_preserving_place_ready_transport_of_normal hhead
  · intro Γ σ σ' head hhead
    exact env_preserving_expr_ready_transport_of_normal hhead
  · intro Γ σ σ' head hhead
    exact env_preserving_stmt_ready_transport_of_normal hhead
  · intro Γ σ σ' head hhead
    exact env_preserving_block_ready_transport_of_normal hhead

end Cpp
