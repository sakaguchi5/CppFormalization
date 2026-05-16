import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalRefinedAssets
import CppFormalization.Cpp2.Core.TypeEnvQuery
import CppFormalization.Cpp2.Core.RuntimeQuery

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalFreshIntro

Theorem-backed fresh-name introduction fragment for the refined
readiness-transport route.

For env-extending heads, the freshly introduced name is not transported from the
pre-world.  It is introduced from the post-state binding guaranteed by the
post-state concrete invariant.

This file proves only the place-readiness introduction facts for the fresh
variable itself:
- `declareObj τ x ov` introduces `.var x` as an object place;
- `declareRef τ x p0` introduces `.var x` as a reference place.

It intentionally does not claim that `load x` is ready.  Load/read readiness
still requires an explicit `CellReadableTyped` witness, as recorded in
`ReadinessTransportNormalRefined.lean`.
-/

/- =========================================================
   1. Top-frame type-declaration witnesses for fresh declarations
   ========================================================= -/

/-- The fresh object declaration is present in the top type frame. -/
theorem typeFrameDeclObject_zero_declareTypeObject
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    typeFrameDeclObject (declareTypeObject Γ x τ) 0 x τ := by
  unfold typeFrameDeclObject declareTypeObject insertTopDecl
  cases Γ.scopes with
  | nil =>
      refine ⟨{ decls := fun y => if y = x then some (.object τ) else none }, ?_, ?_⟩
      · simp
      · simp
  | cons fr frs =>
      refine ⟨{ fr with decls := fun y => if y = x then some (.object τ) else fr.decls y }, ?_, ?_⟩
      · simp
      · simp

/-- The fresh reference declaration is present in the top type frame. -/
theorem typeFrameDeclRef_zero_declareTypeRef
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    typeFrameDeclRef (declareTypeRef Γ x τ) 0 x τ := by
  unfold typeFrameDeclRef declareTypeRef insertTopDecl
  cases Γ.scopes with
  | nil =>
      refine ⟨{ decls := fun y => if y = x then some (.ref τ) else none }, ?_, ?_⟩
      · simp
      · simp
  | cons fr frs =>
      refine ⟨{ fr with decls := fun y => if y = x then some (.ref τ) else fr.decls y }, ?_, ?_⟩
      · simp
      · simp

/- =========================================================
   2. Runtime top-frame binding lookup from realization witnesses
   ========================================================= -/

/-- A top-frame object binding is visible through ordinary runtime lookup. -/
theorem runtimeFrameBindsObject_zero_lookupBinding
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsObject σ 0 x τ a →
    lookupBinding σ x = some (.object τ a) := by
  intro hbindObj
  rcases hbindObj with ⟨fr, hscope, hbind⟩
  cases hσ : σ.scopes with
  | nil =>
      simp [hσ] at hscope
  | cons fr0 frs =>
      have hfr : fr0 = fr := by
        simpa [hσ] using hscope
      subst hfr
      simp [lookupBinding, lookupBindingFrames, hσ, hbind]

/-- A top-frame reference binding is visible through ordinary runtime lookup. -/
theorem runtimeFrameBindsRef_zero_lookupBinding
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsRef σ 0 x τ a →
    lookupBinding σ x = some (.ref τ a) := by
  intro hbindRef
  rcases hbindRef with ⟨fr, hscope, hbind⟩
  cases hσ : σ.scopes with
  | nil =>
      simp [hσ] at hscope
  | cons fr0 frs =>
      have hfr : fr0 = fr := by
        simpa [hσ] using hscope
      subst hfr
      simp [lookupBinding, lookupBindingFrames, hσ, hbind]

/- =========================================================
   3. Fresh-place introduction theorem fragment
   ========================================================= -/

/--
A normal object declaration introduces the fresh variable as a ready object
place in the post world.
-/
theorem declareObj_fresh_object_place_intro_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    DeclareObjFreshObjectPlaceIntroGoal Γ σ σ' τ x ov := by
  intro hctx
  have htyDecl : typeFrameDeclObject (declareTypeObject Γ x τ) 0 x τ :=
    typeFrameDeclObject_zero_declareTypeObject
  rcases hctx.hpost.objectDeclRealized htyDecl with ⟨a, hbindObj, _hown, hlive⟩
  have hlookupDecl : lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
    exact declareObj_lookup_self
  have hlookupBinding : lookupBinding σ' x = some (.object τ a) :=
    runtimeFrameBindsObject_zero_lookupBinding hbindObj
  exact PlaceReadyConcrete.varObject hlookupDecl hlookupBinding hlive

/--
A normal reference declaration introduces the fresh variable as a ready reference
place in the post world.
-/
theorem declareRef_fresh_place_intro_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    DeclareRefFreshPlaceIntroGoal Γ σ σ' τ x p0 := by
  intro hctx
  have htyDecl : typeFrameDeclRef (declareTypeRef Γ x τ) 0 x τ :=
    typeFrameDeclRef_zero_declareTypeRef
  rcases hctx.hpost.refDeclRealized htyDecl with ⟨a, hbindRef, hlive⟩
  have hlookupDecl : lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
    exact declareRef_lookup_self
  have hlookupBinding : lookupBinding σ' x = some (.ref τ a) :=
    runtimeFrameBindsRef_zero_lookupBinding hbindRef
  exact PlaceReadyConcrete.varRef hlookupDecl hlookupBinding hlive

/-- The theorem-backed fresh-name introduction fragment. -/
structure ReadinessTransportNormalFreshIntroFragment : Type where
  declareObjFreshObjectPlaceIntro :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjFreshObjectPlaceIntroGoal Γ σ σ' τ x ov
  declareRefFreshPlaceIntro :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefFreshPlaceIntroGoal Γ σ σ' τ x p0

/-- Current theorem-backed fresh-name introduction fragment. -/
def readinessTransportNormalFreshIntroFragment :
    ReadinessTransportNormalFreshIntroFragment where
  declareObjFreshObjectPlaceIntro := by
    intro Γ σ σ' τ x ov
    exact declareObj_fresh_object_place_intro_of_ctx
  declareRefFreshPlaceIntro := by
    intro Γ σ σ' τ x p0
    exact declareRef_fresh_place_intro_of_ctx

/- =========================================================
   4. Extended known-assets registry
   ========================================================= -/

/--
Known refined assets after adding fresh-place introduction.

This still does not instantiate `ReadinessTransportNormalRefinedSurface`; old-name
stmt/block transport remains a future theorem family.
-/
structure ReadinessTransportNormalRefinedKnownAssetsWithFreshIntro : Type where
  base : ReadinessTransportNormalRefinedKnownAssets
  freshIntro : ReadinessTransportNormalFreshIntroFragment

/-- Current known assets plus theorem-backed fresh-place introduction. -/
def readinessTransportNormalRefinedKnownAssetsWithFreshIntro :
    ReadinessTransportNormalRefinedKnownAssetsWithFreshIntro where
  base := readinessTransportNormalRefinedKnownAssets
  freshIntro := readinessTransportNormalFreshIntroFragment

/-- Thin projection: fresh object place introduction from the extended registry. -/
theorem refinedKnown_declareObj_fresh_object_place_intro
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    DeclareObjFreshObjectPlaceIntroGoal Γ σ σ' τ x ov :=
  readinessTransportNormalRefinedKnownAssetsWithFreshIntro.freshIntro.declareObjFreshObjectPlaceIntro

/-- Thin projection: fresh reference place introduction from the extended registry. -/
theorem refinedKnown_declareRef_fresh_place_intro
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    DeclareRefFreshPlaceIntroGoal Γ σ σ' τ x p0 :=
  readinessTransportNormalRefinedKnownAssetsWithFreshIntro.freshIntro.declareRefFreshPlaceIntro

end Cpp
