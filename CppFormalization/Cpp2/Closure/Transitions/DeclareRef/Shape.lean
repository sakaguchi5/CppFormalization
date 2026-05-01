import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteOwnershipTransport

namespace Cpp

/-!
# Closure.Transitions.DeclareRef.Shape

Type-environment and lookup shape lemmas for `declareTypeRef`.
This layer contains no runtime preservation assembly.
-/

theorem typeFrameDeclObject_declareTypeRef_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
    typeFrameDeclObject Γ k y υ := by
  intro hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      cases k <;>
        simp [declareTypeRef, insertTopDecl, hsc] at hk hdecl
      subst hk
      simp at hdecl
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            simp at hdecl
          · refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclObject, declareTypeRef, insertTopDecl, hsc] using hk
          · simpa [declareTypeRef, insertTopDecl, hsc] using hdecl

theorem typeFrameDeclRef_declareTypeRef_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef (declareTypeRef Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclRef Γ k y υ := by
  intro hfresh hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            left
            simp at hdecl
            exact ⟨rfl, rfl, hdecl.symm⟩
          · right
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          right
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclRef, declareTypeRef, insertTopDecl, hsc] using hk
          · simpa [declareTypeRef, insertTopDecl, hsc] using hdecl

theorem typeFrameDeclObject_declareTypeRef_keep
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
    k ≠ 0 ∨ y ≠ x := by
  intro hty
  cases k with
  | zero =>
      right
      rcases hty with ⟨fr, hk, hdecl⟩
      intro hy
      subst hy
      cases hsc : Γ.scopes <;> {
        simp [declareTypeRef, insertTopDecl, hsc] at hk hdecl
        simp [← hk] at hdecl
      }
  | succ j =>
      left
      simp

theorem typeFrameDeclRef_keep_of_fresh
    {Γ : TypeEnv} {x : Ident}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef Γ k y υ →
    k ≠ 0 ∨ y ≠ x := by
  intro hfresh hty
  cases k with
  | zero =>
      right
      intro hy
      subst hy
      rcases hty with ⟨fr, hk, hdecl⟩
      cases hsc : Γ.scopes with
      | nil =>
          simp [currentTypeScopeFresh, hsc] at hfresh
      | cons fr0 frs =>
          simp [currentTypeScopeFresh, hsc] at hfresh
          simp [hsc] at hk
          subst hk
          rw [hfresh] at hdecl
          simp at hdecl
  | succ j =>
      left
      simp

theorem lookupDecl_declareTypeRef_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeRef, insertTopDecl, hsc]

theorem lookupDecl_declareTypeRef_other
    (Γ : TypeEnv) (x y : Ident) (τ : CppType)
    (hy : y ≠ x) :
    lookupDecl (declareTypeRef Γ x τ) y = lookupDecl Γ y := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeRef, insertTopDecl, hsc, hy]

end Cpp
