import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalFreshRead

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalFreshExpr

Fresh-expression introduction layer for env-extending normal heads.

Stage 5-1 proved fresh `.var x` place readiness.
Stage 5-2 exposed the fresh address and made `load x` ready only under an
explicit `CellReadableTyped` premise.

This file adds the remaining small expression facts for fresh names:
- `addrOf x` is ready after `declareObj` / `declareRef`;
- `addrOf x` evaluates to the fresh address as a `PtrValueReadyAt` witness;
- the Stage 5 assets are consolidated into a single known-assets registry.

This still does not instantiate the full `ReadinessTransportNormalRefinedSurface`:
old-name statement/block transport remains a later theorem family.
-/

/- =========================================================
   1. Fresh `addrOf x` readiness
   ========================================================= -/

/--
A fresh object variable can always have its address taken after the object
declaration.  This is addressability, not readability.
-/
theorem declareObj_fresh_addrOf_ready_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr}
    (hctx : NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov)) :
    ExprReadyConcrete (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) (.ptr τ) := by
  have hp : PlaceReadyConcrete (declareTypeObject Γ x τ) σ' (.var x) τ :=
    declareObj_fresh_object_place_intro_of_ctx hctx
  exact ExprReadyConcrete.addrOf hp

/--
A fresh reference variable can always have its referenced place address taken
after the reference declaration.  This is addressability, not readability.
-/
theorem declareRef_fresh_addrOf_ready_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr}
    (hctx : NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0)) :
    ExprReadyConcrete (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) (.ptr τ) := by
  have hp : PlaceReadyConcrete (declareTypeRef Γ x τ) σ' (.var x) τ :=
    declareRef_fresh_place_intro_of_ctx hctx
  exact ExprReadyConcrete.addrOf hp

/- =========================================================
   2. Fresh `addrOf x` pointer-value witnesses
   ========================================================= -/

/--
After an object declaration, `addrOf x` evaluates to the fresh object address
and is typed as a pointer to the declared object type.
-/
theorem declareObj_fresh_addrOf_ptr_value_ready_at_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr}
    (hctx : NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov)) :
    ∃ a,
      PtrValueReadyAt (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) τ a := by
  rcases declareObj_fresh_object_place_data_of_ctx hctx with
    ⟨a, _hlookupBinding, hplace, _hlive⟩
  have hlookupDecl : lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
    exact declareObj_lookup_self
  have hplaceTy : HasPlaceType (declareTypeObject Γ x τ) (.var x) τ := by
    exact HasPlaceType.var hlookupDecl
  exact ⟨a, ⟨HasValueType.addrOf hplaceTy, BigStepValue.addrOf hplace⟩⟩

/--
After a reference declaration, `addrOf x` evaluates to the address reached
through the fresh reference binding and is typed as a pointer to the referenced
type.
-/
theorem declareRef_fresh_addrOf_ptr_value_ready_at_of_ctx
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr}
    (hctx : NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0)) :
    ∃ a,
      PtrValueReadyAt (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) τ a := by
  rcases declareRef_fresh_place_data_of_ctx hctx with
    ⟨a, _hlookupBinding, hplace, _hlive⟩
  have hlookupDecl : lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
    exact declareRef_lookup_self
  have hplaceTy : HasPlaceType (declareTypeRef Γ x τ) (.var x) τ := by
    exact HasPlaceType.var hlookupDecl
  exact ⟨a, ⟨HasValueType.addrOf hplaceTy, BigStepValue.addrOf hplace⟩⟩

/- =========================================================
   3. Fresh-expression introduction fragment
   ========================================================= -/

/-- The theorem-backed fresh-expression introduction fragment. -/
structure ReadinessTransportNormalFreshExprIntroFragment : Type where
  declareObjFreshAddrOfReady :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
      ExprReadyConcrete (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) (.ptr τ)

  declareRefFreshAddrOfReady :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
      ExprReadyConcrete (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) (.ptr τ)

  declareObjFreshAddrOfPtrValueReadyAt :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
      ∃ a, PtrValueReadyAt (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) τ a

  declareRefFreshAddrOfPtrValueReadyAt :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
      ∃ a, PtrValueReadyAt (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) τ a

/-- Current theorem-backed fresh-expression introduction fragment. -/
def readinessTransportNormalFreshExprIntroFragment :
    ReadinessTransportNormalFreshExprIntroFragment where
  declareObjFreshAddrOfReady := by
    intro Γ σ σ' τ x ov hctx
    exact declareObj_fresh_addrOf_ready_of_ctx hctx
  declareRefFreshAddrOfReady := by
    intro Γ σ σ' τ x p0 hctx
    exact declareRef_fresh_addrOf_ready_of_ctx hctx
  declareObjFreshAddrOfPtrValueReadyAt := by
    intro Γ σ σ' τ x ov hctx
    exact declareObj_fresh_addrOf_ptr_value_ready_at_of_ctx hctx
  declareRefFreshAddrOfPtrValueReadyAt := by
    intro Γ σ σ' τ x p0 hctx
    exact declareRef_fresh_addrOf_ptr_value_ready_at_of_ctx hctx

/- =========================================================
   4. Stage-5 consolidated known-assets registry
   ========================================================= -/

/--
Known refined assets after completing the fresh-name local layer.

This consolidates Stage 5-1 / 5-2 / 5-3 assets:
- fresh place introduction;
- explicit fresh read-condition rules;
- fresh `addrOf` / `PtrValueReadyAt` expression facts.

It still intentionally does not instantiate `ReadinessTransportNormalRefinedSurface`.
-/
structure ReadinessTransportNormalRefinedKnownAssetsWithFresh : Type where
  base : ReadinessTransportNormalRefinedKnownAssetsWithFreshRead
  freshExpr : ReadinessTransportNormalFreshExprIntroFragment

/-- Current refined known assets after the fresh-name local layer. -/
def readinessTransportNormalRefinedKnownAssetsWithFresh :
    ReadinessTransportNormalRefinedKnownAssetsWithFresh where
  base := readinessTransportNormalRefinedKnownAssetsWithFreshRead
  freshExpr := readinessTransportNormalFreshExprIntroFragment

/-- Thin projection: Stage-5 fresh-expression fragment. -/
def refinedKnown_freshExprIntroFragment :
    ReadinessTransportNormalFreshExprIntroFragment :=
  readinessTransportNormalRefinedKnownAssetsWithFresh.freshExpr

/-- Thin projection: fresh object `addrOf x` readiness. -/
theorem refinedKnown_declareObj_fresh_addrOf_ready
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    ExprReadyConcrete (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) (.ptr τ) :=
  refinedKnown_freshExprIntroFragment.declareObjFreshAddrOfReady

/-- Thin projection: fresh reference `addrOf x` readiness. -/
theorem refinedKnown_declareRef_fresh_addrOf_ready
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    ExprReadyConcrete (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) (.ptr τ) :=
  refinedKnown_freshExprIntroFragment.declareRefFreshAddrOfReady

/-- Thin projection: fresh object `addrOf x` pointer-value witness. -/
theorem refinedKnown_declareObj_fresh_addrOf_ptr_value_ready_at
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
    ∃ a, PtrValueReadyAt (declareTypeObject Γ x τ) σ' (.addrOf (.var x)) τ a :=
  refinedKnown_freshExprIntroFragment.declareObjFreshAddrOfPtrValueReadyAt

/-- Thin projection: fresh reference `addrOf x` pointer-value witness. -/
theorem refinedKnown_declareRef_fresh_addrOf_ptr_value_ready_at
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr} :
    NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
    ∃ a, PtrValueReadyAt (declareTypeRef Γ x τ) σ' (.addrOf (.var x)) τ a :=
  refinedKnown_freshExprIntroFragment.declareRefFreshAddrOfPtrValueReadyAt

end Cpp
