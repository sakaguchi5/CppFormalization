import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormal

Normal head-step のあとに、post-env / post-state 側へ readiness を輸送するための
下層 transport kernel の足場。

ここでまだ theorem 本体は入れない。まず theorem-backed に確定してよい
純粋 projection / context packaging だけを切り出す。

狙い:
- `seq_ready_right_after_left_normal` と
  `cons_block_ready_tail_after_head_normal`
  を、最終的には mutual ready-transport theorem family の系へ落とす。
- そのために必要な tail projection と transport context を先に固定する。
-/


/- =========================================================
   1. pure projection lemmas
   ========================================================= -/

/-- Right-tail readiness projection from a ready `seq`. -/
theorem seq_ready_right
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | seq _ ht =>
      exact ht

/-- Tail readiness projection from a ready nonempty block. -/
theorem cons_block_ready_tail
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) →
    BlockReadyConcrete Γ σ ss := by
  intro h
  cases h with
  | cons _ hss =>
      exact hss


/- =========================================================
   2. packaged transport context
   ========================================================= -/

/--
Context for transporting readiness facts across a normal head step.

`Γ, σ` are the pre-state typing/runtime world.
`Δ, σ'` are the post-state typing/runtime world produced by the normal step.
`head` is the statement that performed that transition.
-/
structure NormalTransportCtx
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop where
  hty  : HasTypeStmtCI .normalK Γ head Δ
  hstep : BigStepStmt σ head .normal σ'
  hpost : ScopedTypedStateConcrete Δ σ'


/- =========================================================
   3. target proposition aliases for the future mutual kernel
   ========================================================= -/

/--
Place-readiness transport target across a normal head step.

The transported typing is post-typing over `Δ`, while the incoming readiness
witness still lives in the pre world `Γ, σ`.
-/
abbrev PlaceReadyTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {p : PlaceExpr} {τ : CppType},
    NormalTransportCtx Γ Δ σ σ' head →
    HasPlaceType Δ p τ →
    PlaceReadyConcrete Γ σ p τ →
    PlaceReadyConcrete Δ σ' p τ

/--
Expression-readiness transport target across a normal head step.
-/
abbrev ExprReadyTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {e : ValExpr} {τ : CppType},
    NormalTransportCtx Γ Δ σ σ' head →
    HasValueType Δ e τ →
    ExprReadyConcrete Γ σ e τ →
    ExprReadyConcrete Δ σ' e τ

/--
Statement-readiness transport target across a normal head step.

The tail statement is typed in the post environment `Δ`, with arbitrary control
kind `k`, since readiness itself is control-kind agnostic.
-/
abbrev StmtReadyTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {t : CppStmt},
    NormalTransportCtx Γ Δ σ σ' head →
    HasTypeStmtCI k Δ t Ω →
    StmtReadyConcrete Γ σ t →
    StmtReadyConcrete Δ σ' t

/--
Block-readiness transport target across a normal head step.
-/
abbrev BlockReadyTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {ss : StmtBlock},
    NormalTransportCtx Γ Δ σ σ' head →
    HasTypeBlockCI k Δ ss Ω →
    BlockReadyConcrete Γ σ ss →
    BlockReadyConcrete Δ σ' ss

end Cpp
