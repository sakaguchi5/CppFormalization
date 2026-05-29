import CppFormalization.Cpp2.Effect.NormalHeadContext
import CppFormalization.Cpp2.Effect.SyntaxMention
import CppFormalization.Cpp2.Static.Env.TypeEnv

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.NameEffect

Axiom-free name/environment effect vocabulary for primitive normal heads.

This is the first replacement target for the old Closure-level transport
surfaces: instead of saying that readiness magically transports, we record what
happened to the type environment and to name lookup.
-/

/-- Exact environment preservation for a normal head. -/
structure EnvPreservingEffect
    (Γ Δ : TypeEnv) (head : CppStmt) : Prop where
  sameEnv : Δ = Γ

/-- Object declaration extends the current type environment by a fresh object name. -/
structure DeclareObjNameEffect
    (Γ Δ : TypeEnv) (τ : CppType) (x : Ident) : Prop where
  fresh : currentTypeScopeFresh Γ x
  objectType : ObjectType τ
  postEnv : Δ = declareTypeObject Γ x τ

/-- Reference declaration extends the current type environment by a fresh ref name. -/
structure DeclareRefNameEffect
    (Γ Δ : TypeEnv) (τ : CppType) (x : Ident) (p : PlaceExpr) : Prop where
  fresh : currentTypeScopeFresh Γ x
  placeType : HasPlaceType Γ p τ
  postEnv : Δ = declareTypeRef Γ x τ

/-- Name effect cases for primitive normal heads. -/
inductive NormalHeadNameEffect
    (Γ Δ : TypeEnv) : CppStmt → Prop where
  | skip :
      EnvPreservingEffect Γ Δ .skip →
      NormalHeadNameEffect Γ Δ .skip
  | exprStmt {e : ValExpr} :
      EnvPreservingEffect Γ Δ (.exprStmt e) →
      NormalHeadNameEffect Γ Δ (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      EnvPreservingEffect Γ Δ (.assign p e) →
      NormalHeadNameEffect Γ Δ (.assign p e)
  | declareObjNone {τ : CppType} {x : Ident} :
      DeclareObjNameEffect Γ Δ τ x →
      NormalHeadNameEffect Γ Δ (.declareObj τ x none)
  | declareObjSome {τ : CppType} {x : Ident} {e : ValExpr} :
      DeclareObjNameEffect Γ Δ τ x →
      HasValueType Γ e τ →
      NormalHeadNameEffect Γ Δ (.declareObj τ x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      DeclareRefNameEffect Γ Δ τ x p →
      NormalHeadNameEffect Γ Δ (.declareRef τ x p)

/-! ## Post-environment shapes from CI typing -/

theorem skip_post_env_eq
    {Γ Δ : TypeEnv} :
    HasTypeStmtCI .normalK Γ .skip Δ → Δ = Γ := by
  intro h
  cases h
  rfl

theorem exprStmt_post_env_eq
    {Γ Δ : TypeEnv} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.exprStmt e) Δ → Δ = Γ := by
  intro h
  cases h
  rfl

theorem assign_post_env_eq
    {Γ Δ : TypeEnv} {p : PlaceExpr} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign p e) Δ → Δ = Γ := by
  intro h
  cases h
  rfl

theorem declareObjNone_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x none) Δ →
    currentTypeScopeFresh Γ x ∧ ObjectType τ ∧ Δ = declareTypeObject Γ x τ := by
  intro h
  cases h with
  | declareObjNone hfresh hobj =>
      exact ⟨hfresh, hobj, rfl⟩

theorem declareObjSome_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr} :
    HasTypeStmtCI .normalK Γ (.declareObj τ x (some e)) Δ →
    currentTypeScopeFresh Γ x ∧ ObjectType τ ∧ HasValueType Γ e τ ∧
      Δ = declareTypeObject Γ x τ := by
  intro h
  cases h with
  | declareObjSome hfresh hobj hty =>
      exact ⟨hfresh, hobj, hty, rfl⟩

theorem declareRef_post_env_data
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
    HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ →
    currentTypeScopeFresh Γ x ∧ HasPlaceType Γ p τ ∧ Δ = declareTypeRef Γ x τ := by
  intro h
  cases h with
  | declareRef hfresh hpty =>
      exact ⟨hfresh, hpty, rfl⟩

/-! ## Effect constructors from typing -/

def envPreservingEffect_of_skip_typing
    {Γ Δ : TypeEnv}
    (hty : HasTypeStmtCI .normalK Γ .skip Δ) :
    EnvPreservingEffect Γ Δ .skip :=
  ⟨skip_post_env_eq hty⟩

def envPreservingEffect_of_exprStmt_typing
    {Γ Δ : TypeEnv} {e : ValExpr}
    (hty : HasTypeStmtCI .normalK Γ (.exprStmt e) Δ) :
    EnvPreservingEffect Γ Δ (.exprStmt e) :=
  ⟨exprStmt_post_env_eq hty⟩

def envPreservingEffect_of_assign_typing
    {Γ Δ : TypeEnv} {p : PlaceExpr} {e : ValExpr}
    (hty : HasTypeStmtCI .normalK Γ (.assign p e) Δ) :
    EnvPreservingEffect Γ Δ (.assign p e) :=
  ⟨assign_post_env_eq hty⟩

def declareObjNameEffect_of_none_typing
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident}
    (hty : HasTypeStmtCI .normalK Γ (.declareObj τ x none) Δ) :
    DeclareObjNameEffect Γ Δ τ x := by
  rcases declareObjNone_post_env_data hty with ⟨hfresh, hobj, hΔ⟩
  exact ⟨hfresh, hobj, hΔ⟩

def declareObjNameEffect_of_some_typing
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hty : HasTypeStmtCI .normalK Γ (.declareObj τ x (some e)) Δ) :
    DeclareObjNameEffect Γ Δ τ x := by
  rcases declareObjSome_post_env_data hty with ⟨hfresh, hobj, _htyInit, hΔ⟩
  exact ⟨hfresh, hobj, hΔ⟩

def declareRefNameEffect_of_typing
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hty : HasTypeStmtCI .normalK Γ (.declareRef τ x p) Δ) :
    DeclareRefNameEffect Γ Δ τ x p := by
  rcases declareRef_post_env_data hty with ⟨hfresh, hpty, hΔ⟩
  exact ⟨hfresh, hpty, hΔ⟩

/-! ## Lookup consequences -/

theorem declareObjNameEffect_lookup_fresh
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident}
    (h : DeclareObjNameEffect Γ Δ τ x) :
    lookupDecl Δ x = some (.object τ) := by
  rw [h.postEnv]
  simp

theorem declareObjNameEffect_lookup_old
    {Γ Δ : TypeEnv} {τ : CppType} {x y : Ident}
    (h : DeclareObjNameEffect Γ Δ τ x) :
    y ≠ x → lookupDecl Δ y = lookupDecl Γ y := by
  intro hxy
  rw [h.postEnv]
  exact lookupDecl_declareTypeObject_other Γ τ hxy

theorem declareRefNameEffect_lookup_fresh
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (h : DeclareRefNameEffect Γ Δ τ x p) :
    lookupDecl Δ x = some (.ref τ) := by
  rw [h.postEnv]
  simp

theorem declareRefNameEffect_lookup_old
    {Γ Δ : TypeEnv} {τ : CppType} {x y : Ident} {p : PlaceExpr}
    (h : DeclareRefNameEffect Γ Δ τ x p) :
    y ≠ x → lookupDecl Δ y = lookupDecl Γ y := by
  intro hxy
  rw [h.postEnv]
  exact lookupDecl_declareTypeRef_other Γ τ hxy

end Cpp
