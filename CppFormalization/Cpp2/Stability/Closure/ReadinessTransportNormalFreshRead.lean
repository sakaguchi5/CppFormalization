import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalFreshIntro

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalFreshRead

Read-condition layer for fresh names introduced by env-extending normal heads.

`ReadinessTransportNormalFreshIntro.lean` proves that a fresh declaration makes
`.var x` a ready place in the post world.  This file deliberately does not try
to derive load/read readiness from that alone.

Instead, it exposes the post-state address of the fresh variable and proves the
small read rule under an explicit `CellReadableTyped` assumption.  This keeps the
C++ meaning honest: a fresh object declared without an initializer is a valid
place, but not necessarily readable.
-/

/- =========================================================
   1. Fresh variable address data from the post invariant
   ========================================================= -/

/--
A fresh object declaration exposes the runtime address of the new object place.
-/
theorem declareObj_fresh_object_place_data_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    ∃ a,
      lookupBinding σ' x = some (.object τ a) ∧
      BigStepPlace σ' (.var x) a ∧
      CellLiveTyped σ' a τ := by
  intro hctx
  have htyDecl : typeFrameDeclObject (declareTypeObject Γ x τ) 0 x τ :=
    typeFrameDeclObject_zero_declareTypeObject
  rcases hctx.hpost.objectDeclRealized htyDecl with ⟨a, hbindObj, _hown, hlive⟩
  have hlookupBinding : lookupBinding σ' x = some (.object τ a) :=
    runtimeFrameBindsObject_zero_lookupBinding hbindObj
  exact ⟨a, hlookupBinding, BigStepPlace.varObject hlookupBinding, hlive⟩

/--
A fresh reference declaration exposes the runtime address of the referenced
place reached through the new reference binding.
-/
theorem declareRef_fresh_place_data_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    ∃ a,
      lookupBinding σ' x = some (.ref τ a) ∧
      BigStepPlace σ' (.var x) a ∧
      CellLiveTyped σ' a τ := by
  intro hctx
  have htyDecl : typeFrameDeclRef (declareTypeRef Γ x τ) 0 x τ :=
    typeFrameDeclRef_zero_declareTypeRef
  rcases hctx.hpost.refDeclRealized htyDecl with ⟨a, hbindRef, hlive⟩
  have hlookupBinding : lookupBinding σ' x = some (.ref τ a) :=
    runtimeFrameBindsRef_zero_lookupBinding hbindRef
  exact ⟨a, hlookupBinding, BigStepPlace.varRef hlookupBinding, hlive⟩

/- =========================================================
   2. Fresh load readiness under explicit read conditions
   ========================================================= -/

/--
A fresh object variable can be loaded only when its fresh object cell is known to
be readable/initialized.

This is intentionally stronger than fresh place introduction: `declareObj τ x
none` gives a ready place, but not this theorem's `CellReadableTyped` premise.
-/
theorem declareObj_fresh_object_load_ready_of_ctx_and_readable
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr}
    (hctx : NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov))
    (hread : ∀ {a : Nat}, lookupBinding σ' x = some (.object τ a) → CellReadableTyped σ' a τ) :
    ExprReadyConcrete (declareTypeObject Γ x τ) σ' (.load (.var x)) τ := by
  rcases declareObj_fresh_object_place_data_of_ctx hctx with
    ⟨a, hlookupBinding, hplace, _hlive⟩
  have hp : PlaceReadyConcrete (declareTypeObject Γ x τ) σ' (.var x) τ :=
    declareObj_fresh_object_place_intro_of_ctx hctx
  exact readinessTransportRefined_load_ready_of_place_and_readable
    hp hplace (hread hlookupBinding)

/--
A fresh reference variable can be loaded only when the referenced target cell is
known to be readable/initialized.
-/
theorem declareRef_fresh_load_ready_of_ctx_and_readable
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr}
    (hctx : NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0))
    (hread : ∀ {a : Nat}, lookupBinding σ' x = some (.ref τ a) → CellReadableTyped σ' a τ) :
    ExprReadyConcrete (declareTypeRef Γ x τ) σ' (.load (.var x)) τ := by
  rcases declareRef_fresh_place_data_of_ctx hctx with
    ⟨a, hlookupBinding, hplace, _hlive⟩
  have hp : PlaceReadyConcrete (declareTypeRef Γ x τ) σ' (.var x) τ :=
    declareRef_fresh_place_intro_of_ctx hctx
  exact readinessTransportRefined_load_ready_of_place_and_readable
    hp hplace (hread hlookupBinding)

/-- The theorem-backed read-condition fragment for fresh names. -/
structure ReadinessTransportNormalFreshReadFragment : Type where
  declareObjFreshObjectPlaceData :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
      ∃ a,
        lookupBinding σ' x = some (.object τ a) ∧
        BigStepPlace σ' (.var x) a ∧
        CellLiveTyped σ' a τ

  declareRefFreshPlaceData :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
      ∃ a,
        lookupBinding σ' x = some (.ref τ a) ∧
        BigStepPlace σ' (.var x) a ∧
        CellLiveTyped σ' a τ

  declareObjFreshObjectLoadReady :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      (hctx : NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov)) →
      (∀ {a : Nat}, lookupBinding σ' x = some (.object τ a) → CellReadableTyped σ' a τ) →
      ExprReadyConcrete (declareTypeObject Γ x τ) σ' (.load (.var x)) τ

  declareRefFreshLoadReady :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      (hctx : NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0)) →
      (∀ {a : Nat}, lookupBinding σ' x = some (.ref τ a) → CellReadableTyped σ' a τ) →
      ExprReadyConcrete (declareTypeRef Γ x τ) σ' (.load (.var x)) τ

/-- Current theorem-backed read-condition fragment for fresh names. -/
def readinessTransportNormalFreshReadFragment :
    ReadinessTransportNormalFreshReadFragment where
  declareObjFreshObjectPlaceData := by
    intro Γ σ σ' τ x ov hctx
    exact declareObj_fresh_object_place_data_of_ctx hctx
  declareRefFreshPlaceData := by
    intro Γ σ σ' τ x p0 hctx
    exact declareRef_fresh_place_data_of_ctx hctx
  declareObjFreshObjectLoadReady := by
    intro Γ σ σ' τ x ov hctx hread
    exact declareObj_fresh_object_load_ready_of_ctx_and_readable hctx hread
  declareRefFreshLoadReady := by
    intro Γ σ σ' τ x p0 hctx hread
    exact declareRef_fresh_load_ready_of_ctx_and_readable hctx hread

/--
Known refined assets after adding fresh-place introduction and explicit fresh
read-condition rules.
-/
structure ReadinessTransportNormalRefinedKnownAssetsWithFreshRead : Type where
  base : ReadinessTransportNormalRefinedKnownAssetsWithFreshIntro
  freshRead : ReadinessTransportNormalFreshReadFragment

/-- Current known assets plus theorem-backed fresh read-condition rules. -/
def readinessTransportNormalRefinedKnownAssetsWithFreshRead :
    ReadinessTransportNormalRefinedKnownAssetsWithFreshRead where
  base := readinessTransportNormalRefinedKnownAssetsWithFreshIntro
  freshRead := readinessTransportNormalFreshReadFragment

/-- Thin projection: fresh object place data from the extended registry. -/
theorem refinedKnown_declareObj_fresh_object_place_data
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    ∃ a,
      lookupBinding σ' x = some (.object τ a) ∧
      BigStepPlace σ' (.var x) a ∧
      CellLiveTyped σ' a τ :=
  readinessTransportNormalRefinedKnownAssetsWithFreshRead.freshRead.declareObjFreshObjectPlaceData

/-- Thin projection: fresh reference place data from the extended registry. -/
theorem refinedKnown_declareRef_fresh_place_data
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    ∃ a,
      lookupBinding σ' x = some (.ref τ a) ∧
      BigStepPlace σ' (.var x) a ∧
      CellLiveTyped σ' a τ :=
  readinessTransportNormalRefinedKnownAssetsWithFreshRead.freshRead.declareRefFreshPlaceData

end Cpp
