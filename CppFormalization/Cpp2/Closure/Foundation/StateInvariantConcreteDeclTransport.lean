import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteDeclTransport

Reusable decl-transport API extracted from full assembly.

This file intentionally keeps only the generic type-env side transport facts:
- succ-frame invariance under top-frame declaration updates
- zero-frame recovery of old declarations when the updated name/kind does not match

It does **not** reintroduce the purely local nonempty/lookup helpers that were only
wrapping one-shot `cases`/`simp` work.
-/
-- スコープリストの先頭を差し替えても、k.succ 番目の要素は不変であることを示す補題
theorem getElem_succ_insertTop_iff {scopes : List TypeFrame} {fr0' : TypeFrame} {k : Nat} {fr : TypeFrame} :
    (fr0' :: scopes.tail)[k.succ]? = some fr ↔ scopes[k.succ]? = some fr := by
  cases scopes with
  | nil => simp
  | cons fr0 frs => simp

-- 1. 共通の基盤
theorem scopes_declare_succ_iff {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} {fr : TypeFrame} {is_ref : Bool} :
    (if is_ref then declareTypeRef Γ x τ else declareTypeObject Γ x τ).scopes[k.succ]? = some fr ↔
    Γ.scopes[k.succ]? = some fr := by
  split <;> cases hsc : Γ.scopes <;> simp [declareTypeRef, declareTypeObject, insertTopDecl, hsc]

-- 2. 特化補題（Object用）
theorem scopes_declareTypeObject_succ_iff {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} {fr : TypeFrame} :
    (declareTypeObject Γ x τ).scopes[k.succ]? = some fr ↔ Γ.scopes[k.succ]? = some fr :=
  @scopes_declare_succ_iff Γ x τ k fr false

-- 3. 特化補題（Ref用）
theorem scopes_declareTypeRef_succ_iff {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} {fr : TypeFrame} :
    (declareTypeRef Γ x τ).scopes[k.succ]? = some fr ↔ Γ.scopes[k.succ]? = some fr :=
  @scopes_declare_succ_iff Γ x τ k fr true

@[simp] theorem typeFrameDeclObject_declareTypeObject_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclObject (declareTypeObject Γ x τ) k.succ y υ ↔
      typeFrameDeclObject Γ k.succ y υ := by
  constructor <;> rintro ⟨fr, hk, hb⟩
  · -- 特化補題を使って hk を直接書き換え
    rw [scopes_declareTypeObject_succ_iff] at hk
    exact ⟨fr, hk, hb⟩
  · -- mpr
    refine ⟨fr, ?_, hb⟩ -- ゴールの typeFrame... を分解して scopes[k.succ]? = some fr を露出させる
    rw [scopes_declareTypeObject_succ_iff]
    exact hk

@[simp] theorem typeFrameDeclRef_declareTypeObject_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclRef (declareTypeObject Γ x τ) k.succ y υ ↔
      typeFrameDeclRef Γ k.succ y υ := by
  constructor <;> rintro ⟨fr, hk, hb⟩
  · rw [scopes_declareTypeObject_succ_iff] at hk
    exact ⟨fr, hk, hb⟩
  · refine ⟨fr, ?_, hb⟩
    rw [scopes_declareTypeObject_succ_iff]
    exact hk

@[simp] theorem typeFrameDeclObject_declareTypeRef_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k.succ y υ ↔
      typeFrameDeclObject Γ k.succ y υ := by
  constructor <;> rintro ⟨fr, hk, hb⟩
  · rw [scopes_declareTypeRef_succ_iff] at hk
    exact ⟨fr, hk, hb⟩
  · refine ⟨fr, ?_, hb⟩
    rw [scopes_declareTypeRef_succ_iff]
    exact hk

@[simp] theorem typeFrameDeclRef_declareTypeRef_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclRef (declareTypeRef Γ x τ) k.succ y υ ↔
      typeFrameDeclRef Γ k.succ y υ := by
  constructor <;> rintro ⟨fr, hk, hb⟩
  · rw [scopes_declareTypeRef_succ_iff] at hk
    exact ⟨fr, hk, hb⟩
  · refine ⟨fr, ?_, hb⟩
    rw [scopes_declareTypeRef_succ_iff]
    exact hk

theorem typeFrameDeclObject_declareTypeObject_zero_old_of_ne
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    (hx' : x' ≠ x) :
    typeFrameDeclObject (declareTypeObject Γ x τ) 0 x' τ' →
      typeFrameDeclObject Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [declareTypeObject, insertTopDecl, hsc] at hk
      subst Γfr'
      simp at hb
      simp [hx'] at hb
  | cons fr0 frs =>
      simp [declareTypeObject, insertTopDecl, hsc] at hk
      subst Γfr'
      have hbOld : fr0.decls x' = some (.object τ') := by
        simpa [hx'] using hb
      exact ⟨fr0, by simp [hsc], hbOld⟩

theorem typeFrameDeclRef_declareTypeRef_zero_old_of_ne
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    (hx' : x' ≠ x) :
    typeFrameDeclRef (declareTypeRef Γ x τ) 0 x' τ' →
      typeFrameDeclRef Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [declareTypeRef, insertTopDecl, hsc] at hk
      subst Γfr'
      simp at hb
      simp [hx'] at hb
  | cons fr0 frs =>
      simp [declareTypeRef, insertTopDecl, hsc] at hk
      subst Γfr'
      have hbOld : fr0.decls x' = some (.ref τ') := by
        simpa [hx'] using hb
      exact ⟨fr0, by simp [hsc], hbOld⟩

theorem typeFrameDeclRef_declareTypeObject_zero_old
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType} :
    typeFrameDeclRef (declareTypeObject Γ x τ) 0 x' τ' →
      typeFrameDeclRef Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [declareTypeObject, insertTopDecl, hsc] at hk
      subst Γfr'
      simp at hb
  | cons fr0 frs =>
      simp [declareTypeObject, insertTopDecl, hsc] at hk
      subst Γfr'
      have hx' : x' ≠ x := by
        intro hEq
        subst x'
        simp at hb
      have hbOld : fr0.decls x' = some (.ref τ') := by
        simpa [hx'] using hb
      exact ⟨fr0, by simp [hsc], hbOld⟩

theorem typeFrameDeclObject_declareTypeRef_zero_old
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) 0 x' τ' →
      typeFrameDeclObject Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [declareTypeRef, insertTopDecl, hsc] at hk
      subst Γfr'
      simp at hb
  | cons fr0 frs =>
      simp [declareTypeRef, insertTopDecl, hsc] at hk
      subst Γfr'
      have hx' : x' ≠ x := by
        intro hEq
        subst x'
        simp at hb
      have hbOld : fr0.decls x' = some (.object τ') := by
        simpa [hx'] using hb
      exact ⟨fr0, by simp [hsc], hbOld⟩

end Cpp
