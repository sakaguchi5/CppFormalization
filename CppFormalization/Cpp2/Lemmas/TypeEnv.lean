import CppFormalization.Cpp2.Core.TypeEnv

/-!
Lookup algebra for the scoped type environment.
-/

namespace Cpp

/-!  Type-environment lookup algebra. -/

@[simp] theorem lookupDecl_pushTypeScope (Γ : TypeEnv) (x : Ident) :
    lookupDecl (pushTypeScope Γ) x = lookupDecl Γ x := by
  rfl

@[simp] theorem lookupDecl_insertTopDecl_self
    (Γ : TypeEnv) (x : Ident) (d : DeclInfo) :
    lookupDecl (insertTopDecl Γ x d) x = some d := by
  unfold lookupDecl insertTopDecl lookupDeclFrames
  cases hsc : Γ.scopes with
  | nil =>
      simp
  | cons fr frs =>
      simp

@[simp] theorem lookupDecl_insertTopDecl_other
    (Γ : TypeEnv) {x y : Ident} (d : DeclInfo) (hxy : y ≠ x) :
    lookupDecl (insertTopDecl Γ x d) y = lookupDecl Γ y := by
  unfold lookupDecl insertTopDecl lookupDeclFrames
  cases hsc : Γ.scopes with
  | nil =>
      simp only
      unfold lookupDeclFrames
      simp [hxy]
  | cons fr frs =>
      simp [hxy]

@[simp] theorem lookupDecl_declareTypeObject_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
  simp [declareTypeObject, lookupDecl_insertTopDecl_self Γ x (.object τ)]

@[simp] theorem lookupDecl_declareTypeRef_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
  simp [declareTypeRef, lookupDecl_insertTopDecl_self Γ x (.ref τ)]

@[simp] theorem lookupDecl_declareTypeObject_other
    (Γ : TypeEnv) {x y : Ident} (τ : CppType) (hxy : y ≠ x) :
    lookupDecl (declareTypeObject Γ x τ) y = lookupDecl Γ y := by
  simpa [declareTypeObject] using
    lookupDecl_insertTopDecl_other Γ (.object τ) hxy

@[simp] theorem lookupDecl_declareTypeRef_other
    (Γ : TypeEnv) {x y : Ident} (τ : CppType) (hxy : y ≠ x) :
    lookupDecl (declareTypeRef Γ x τ) y = lookupDecl Γ y := by
  simpa [declareTypeRef] using
    lookupDecl_insertTopDecl_other Γ (.ref τ) hxy

end Cpp
