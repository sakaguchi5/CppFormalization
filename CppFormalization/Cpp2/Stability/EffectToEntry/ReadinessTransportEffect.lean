import CppFormalization.Cpp2.Effect.NormalHeadEffect

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.ReadinessTransportEffect

Effect-indexed readiness transport targets.

This file deliberately does not prove the full transport theorem and introduces
no axiom.  It fixes the non-Closure target shape that future proofs should
instantiate: readiness is transported or introduced because a concrete
`NormalHeadEffect` says what the head changed.
-/

namespace NormalHeadEffect

/--
The identifier freshly introduced by an env-extending normal head, if any.

Env-preserving heads return `none`.  Declaration heads return the declared name.
This lets transport targets be indexed by the actual effect certificate instead
of silently falling back to an unrestricted transport goal.
-/
def freshIdent?
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Option Ident :=
  match eff with
  | .skip _ _ =>
      none
  | .exprStmt _ _ =>
      none
  | .assign _ _ =>
      none
  | .declareObjNone (x := x) _ _ =>
      some x
  | .declareObjSome (x := x) _ _ _ _ =>
      some x
  | .declareRef (x := x) _ _ _ =>
      some x

end NormalHeadEffect

/--
A place target is preserved by an effect when it is not the freshly introduced
name of an env-extending head.

For env-preserving heads this is currently vacuous.  Heap/read-sensitive
restrictions for assignment can later be added by strengthening this predicate,
without changing the transport package shape.
-/
abbrev PlaceTargetPreservedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head)
    (p : PlaceExpr) : Prop :=
  match NormalHeadEffect.freshIdent? eff with
  | none => True
  | some fresh => EffectPlaceDoesNotMentionIdent fresh p

/-- Expression targets preserved by the name component of an effect. -/
abbrev ExprTargetPreservedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head)
    (e : ValExpr) : Prop :=
  match NormalHeadEffect.freshIdent? eff with
  | none => True
  | some fresh => EffectExprDoesNotMentionIdent fresh e

/-- Statement targets preserved by the name component of an effect. -/
abbrev StmtTargetPreservedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head)
    (st : CppStmt) : Prop :=
  match NormalHeadEffect.freshIdent? eff with
  | none => True
  | some fresh => EffectStmtDoesNotMentionIdent fresh st

/-- Block targets preserved by the name component of an effect. -/
abbrev BlockTargetPreservedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head)
    (ss : StmtBlock) : Prop :=
  match NormalHeadEffect.freshIdent? eff with
  | none => True
  | some fresh => EffectBlockDoesNotMentionIdent fresh ss

/--
Place-readiness transport indexed by an explicit normal-head effect.

This is now genuinely effect-indexed: declaration effects only transport old-name
targets.  Fresh-name targets are introduced by separate fresh-introduction
theorems below.
-/
abbrev PlaceReadyTransportByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  ∀ {p : PlaceExpr} {τ : CppType},
    PlaceTargetPreservedByEffect eff p →
    HasPlaceType Δ p τ →
    PlaceReadyConcrete Γ σ p τ →
    PlaceReadyConcrete Δ σ' p τ

/-- Expression-readiness transport indexed by an explicit normal-head effect. -/
abbrev ExprReadyTransportByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  ∀ {e : ValExpr} {τ : CppType},
    ExprTargetPreservedByEffect eff e →
    HasValueType Δ e τ →
    ExprReadyConcrete Γ σ e τ →
    ExprReadyConcrete Δ σ' e τ

/-- Statement-readiness transport indexed by an explicit normal-head effect. -/
abbrev StmtReadyTransportByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {st : CppStmt},
    StmtTargetPreservedByEffect eff st →
    HasTypeStmtCI k Δ st Ω →
    StmtReadyConcrete Γ σ st →
    StmtReadyConcrete Δ σ' st

/-- Block-readiness transport indexed by an explicit normal-head effect. -/
abbrev BlockReadyTransportByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {ss : StmtBlock},
    BlockTargetPreservedByEffect eff ss →
    HasTypeBlockCI k Δ ss Ω →
    BlockReadyConcrete Γ σ ss →
    BlockReadyConcrete Δ σ' ss

/--
A future complete effect-indexed readiness package.

Unlike the old unrestricted Closure core, this package is parameterized by an
explicit effect certificate.  Constructing this package for each head class is
the next proof task; merely defining the target is axiom-free.
-/
structure ReadinessTransportEffectPackage
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Type where
  place : PlaceReadyTransportByEffect eff
  expr : ExprReadyTransportByEffect eff
  stmt : StmtReadyTransportByEffect eff
  block : BlockReadyTransportByEffect eff

/-- Fresh object place introduction from a declaration name effect and post invariant.

This is not transport from the pre-state.  The fresh variable is introduced from
the post-state binding certified by the post invariant.
-/
theorem declareObj_effect_fresh_object_place_ready
    {Γ Δ : TypeEnv} {σ' : State} {τ : CppType} {x : Ident}
    (hname : DeclareObjNameEffect Γ Δ τ x)
    (hpost : ScopedTypedStateConcrete Δ σ') :
    PlaceReadyConcrete Δ σ' (.var x) τ := by
  rw [hname.postEnv] at hpost ⊢
  exact declareObj_fresh_object_place_ready_of_post hpost

/-- Fresh reference place introduction from a declaration name effect and post invariant.

This is not transport from the pre-state.  The fresh reference variable is
introduced from the post-state binding certified by the post invariant.
-/
theorem declareRef_effect_fresh_place_ready
    {Γ Δ : TypeEnv} {σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr}
    (hname : DeclareRefNameEffect Γ Δ τ x p0)
    (hpost : ScopedTypedStateConcrete Δ σ') :
    PlaceReadyConcrete Δ σ' (.var x) τ := by
  rw [hname.postEnv] at hpost ⊢
  exact declareRef_fresh_place_ready_of_post hpost

end Cpp
