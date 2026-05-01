import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormal
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalEnvExtending

Theorem-backed shape layer for env-extending normal heads.

At this point in the development, the true hard part of
`ReadinessTransportNormalCore` is no longer the env-preserving fragment
(`skip / exprStmt / assign`), but the heads that *change* the post environment:
- `declareObj τ x none`
- `declareObj τ x (some e)`
- `declareRef τ x p`

This file does **not** yet prove the full readiness transport theorems for those
heads. That would require the later old-name / fresh-name case split on places,
expressions, statements, and blocks.

Instead, this file fixes the theorem-backed *shape* facts that any future proof
must use:
- which heads are env-extending;
- what exact post environment shape each such head produces;
- how to read the same data back from a `NormalTransportCtx`.
-/


/- =========================================================
   1. env-extending head class
   ========================================================= -/

/--
Current normal heads that extend the ambient type environment.
-/
def EnvExtendingNormalHead : CppStmt → Prop
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | _ => False

theorem env_extending_normal_head_not_replay_stable
    {head : CppStmt} :
    EnvExtendingNormalHead head →
    ¬ ReplayStablePrimitiveStmt head := by
  intro hhead hstable
  cases head <;> simp [EnvExtendingNormalHead, ReplayStablePrimitiveStmt] at hhead hstable

theorem env_extending_normal_head_cases
    {head : CppStmt} :
    EnvExtendingNormalHead head →
      (∃ τ x ov, head = .declareObj τ x ov) ∨
      (∃ τ x p, head = .declareRef τ x p) := by
  intro hhead
  cases head <;> simp [EnvExtendingNormalHead] at hhead
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr ⟨_, _, _, rfl⟩


/- =========================================================
   2. exact post-environment shape for env-extending heads
   ========================================================= -/

theorem declareObjNone_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x none) Δ →
    currentTypeScopeFresh Γ x ∧
    ObjectType τ ∧
    Δ = declareTypeObject Γ x τ := by
  intro h
  cases h with
  | declareObjNone hfresh hobj =>
      exact ⟨hfresh, hobj, rfl⟩

theorem declareObjSome_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x (some e)) Δ →
    currentTypeScopeFresh Γ x ∧
    ObjectType τ ∧
    HasValueType Γ e τ ∧
    Δ = declareTypeObject Γ x τ := by
  intro h
  cases h with
  | declareObjSome hfresh hobj hv =>
      exact ⟨hfresh, hobj, hv, rfl⟩

theorem declareRef_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    currentTypeScopeFresh Γ x ∧
    HasPlaceType Γ p τ ∧
    Δ = declareTypeRef Γ x τ := by
  intro h
  cases h with
  | declareRef hfresh hp =>
      exact ⟨hfresh, hp, rfl⟩

theorem env_extending_normal_head_post_env_shape
    {Γ Δ : TypeEnv} {head : CppStmt} :
    EnvExtendingNormalHead head →
    HasTypeStmtCI .normalK Γ head Δ →
      (∃ x τ, Δ = declareTypeObject Γ x τ) ∨
      (∃ x τ, Δ = declareTypeRef Γ x τ) := by
  intro hhead hty
  cases head <;> simp [EnvExtendingNormalHead] at hhead
  case declareObj τ x ov =>
    -- ここで ov (Option ValExpr) が none か some e かで分岐させる
    cases ov with
    | none =>
      rcases declareObjNone_post_env_data hty with ⟨_, _, hΔ⟩
      exact Or.inl ⟨x, τ, hΔ⟩
    | some e =>
      rcases declareObjSome_post_env_data hty with ⟨_, _, _, hΔ⟩
      exact Or.inl ⟨x, τ, hΔ⟩
  case declareRef τ x p =>
    rcases declareRef_post_env_data hty with ⟨_, _, hΔ⟩
    exact Or.inr ⟨x, τ, hΔ⟩


/- =========================================================
   3. ctx-level post-environment shape
   ========================================================= -/

theorem env_extending_normal_ctx_post_env_shape
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvExtendingNormalHead head →
    NormalTransportCtx Γ Δ σ σ' head →
      (∃ x τ, Δ = declareTypeObject Γ x τ) ∨
      (∃ x τ, Δ = declareTypeRef Γ x τ) := by
  intro hhead hctx
  exact env_extending_normal_head_post_env_shape hhead hctx.hty


/- =========================================================
   4. future obligation aliases
   ========================================================= -/

/--
Future place-transport obligation for object-declaration heads.

Intended reading:
after a normal `declareObj`, post-typed places should be transported from the
pre world to the post world by splitting on whether they mention the fresh name
or only old names.
-/
abbrev DeclareObjPlaceTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option ValExpr) : Prop :=
  ∀ {p : PlaceExpr} {τp : CppType},
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    HasPlaceType (declareTypeObject Γ x τ) p τp →
    PlaceReadyConcrete Γ σ p τp →
    PlaceReadyConcrete (declareTypeObject Γ x τ) σ' p τp

/--
Future place-transport obligation for reference-declaration heads.
-/
abbrev DeclareRefPlaceTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (p0 : PlaceExpr) : Prop :=
  ∀ {p : PlaceExpr} {τp : CppType},
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    HasPlaceType (declareTypeRef Γ x τ) p τp →
    PlaceReadyConcrete Γ σ p τp →
    PlaceReadyConcrete (declareTypeRef Γ x τ) σ' p τp

/--
Future statement-transport obligation for object-declaration heads.
-/
abbrev DeclareObjStmtTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option ValExpr) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {st : CppStmt},
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    HasTypeStmtCI k (declareTypeObject Γ x τ) st Ω →
    StmtReadyConcrete Γ σ st →
    StmtReadyConcrete (declareTypeObject Γ x τ) σ' st

/--
Future block-transport obligation for reference-declaration heads.
-/
abbrev DeclareRefBlockTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (p0 : PlaceExpr) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {ss : StmtBlock},
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    HasTypeBlockCI k (declareTypeRef Γ x τ) ss Ω →
    BlockReadyConcrete Γ σ ss →
    BlockReadyConcrete (declareTypeRef Γ x τ) σ' ss

end Cpp
