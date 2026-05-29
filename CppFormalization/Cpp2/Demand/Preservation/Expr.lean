import CppFormalization.Cpp2.Entry.StaticSafety.Readiness

namespace Cpp

/-!
# Proof.Preservation.Demand.Expr

Execution-demand vocabulary for expression and place readiness.

The old ` 削除済み` treated readiness as something that can be
transported across an arbitrary normal step.  That is too strong: readiness is
state-sensitive.  This file deliberately keeps the expression/place layer small:
a demand at a program point is exactly the concrete readiness required at that
program point.
-/

/--
Demand that a place can be used at the current program point.

This is an alias rather than a new copy of the old predicate: the conceptual
change is not the local place condition itself, but where and when it is
required.  A later statement must demand its places at its own entry state, not
transport old readiness through an unrelated previous statement.
-/
abbrev PlaceExecutionDemand
    (Γ : TypeEnv) (σ : State) (p : PlaceExpr) (τ : CppType) : Prop :=
  PlaceReadyConcrete Γ σ p τ

/--
Demand that an expression can be evaluated at the current program point.
-/
abbrev ExprExecutionDemand
    (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) : Prop :=
  ExprReadyConcrete Γ σ e τ

@[simp] theorem placeDemand_iff_ready
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceExecutionDemand Γ σ p τ ↔ PlaceReadyConcrete Γ σ p τ := by
  rfl

@[simp] theorem exprDemand_iff_ready
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprExecutionDemand Γ σ e τ ↔ ExprReadyConcrete Γ σ e τ := by
  rfl

/--
A small package used by statement-demand constructors for expression evaluation.
It records both the static type/readiness demand and the actual value produced
by the semantics at that same state.
-/
structure ExprEvalDemand
    (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) (v : Value) : Prop where
  typed : HasValueType Γ e τ
  ready : ExprExecutionDemand Γ σ e τ
  eval  : BigStepValue σ e v

/--
A small package used by assignment/reference-declaration constructors for place
evaluation.
-/
structure PlaceEvalDemand
    (Γ : TypeEnv) (σ : State) (p : PlaceExpr) (τ : CppType) (a : Nat) : Prop where
  typed : HasPlaceType Γ p τ
  ready : PlaceExecutionDemand Γ σ p τ
  eval  : BigStepPlace σ p a

end Cpp
