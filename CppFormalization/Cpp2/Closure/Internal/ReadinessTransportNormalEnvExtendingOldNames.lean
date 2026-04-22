import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalEnvExtendingNames

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalEnvExtendingOldNames

Reusable old-name branch for env-extending normal heads.

`ReadinessTransportNormalEnvExtendingNames` established the raw lookup/freshness
algebra. This file repackages the part that will actually be reused in later
transport proofs:

- object declaration, old name `y ≠ x`
- reference declaration, old name `y ≠ x`

The point is to make the future transport proofs split cleanly into

1. old-name branch: reduce to the pre world
2. fresh-name branch: use declaration-specific runtime facts

without re-deriving the context-level environment equations every time.
-/


/- =========================================================
   1. object-declaration old-name branch
   ========================================================= -/

theorem declareObj_ctx_old_name_lookup_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    lookupDecl Δ y = lookupDecl Γ y := by
  intro hxy hctx
  have hΔ : Δ = declareTypeObject Γ x τ := by
    cases ov with
    | none =>
        rcases declareObjNone_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, hΔ⟩
        exact hΔ
    | some e =>
        rcases declareObjSome_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, _hv, hΔ⟩
        exact hΔ
  subst hΔ
  exact declareObj_lookup_other hxy

theorem declareObj_ctx_old_name_freshness_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr}
    (hneΓ : TypeEnvNonempty Γ)
    (hxy : y ≠ x)
    (hctx : NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov)) :
    currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y := by
  have hΔ : Δ = declareTypeObject Γ x τ := by
    cases ov with
    | none =>
        rcases declareObjNone_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, hΔ⟩
        exact hΔ
    | some e =>
        rcases declareObjSome_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, _hv, hΔ⟩
        exact hΔ
  subst hΔ
  exact currentTypeScopeFresh_declareObj_other_iff hneΓ hxy

theorem declareObj_ctx_fresh_name_lookup_object
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    lookupDecl Δ x = some (.object τ) := by
  intro hctx
  have hΔ : Δ = declareTypeObject Γ x τ := by
    cases ov with
    | none =>
        rcases declareObjNone_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, hΔ⟩
        exact hΔ
    | some e =>
        rcases declareObjSome_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, _hv, hΔ⟩
        exact hΔ
  subst hΔ
  simp

theorem declareObj_ctx_fresh_name_not_fresh
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {ov : Option ValExpr} :
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    ¬ currentTypeScopeFresh Δ x := by
  intro hctx
  have hΔ : Δ = declareTypeObject Γ x τ := by
    cases ov with
    | none =>
        rcases declareObjNone_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, hΔ⟩
        exact hΔ
    | some e =>
        rcases declareObjSome_post_env_data hctx.hty with
          ⟨_hfresh, _hobj, _hv, hΔ⟩
        exact hΔ
  subst hΔ
  exact currentTypeScopeFresh_declareObj_self_false


/- =========================================================
   2. reference-declaration old-name branch
   ========================================================= -/

theorem declareRef_ctx_old_name_lookup_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    lookupDecl Δ y = lookupDecl Γ y := by
  intro hxy hctx
  have hΔ : Δ = declareTypeRef Γ x τ := by
    rcases declareRef_post_env_data hctx.hty with
      ⟨_hfresh, _hp, hΔ⟩
    exact hΔ
  subst hΔ
  exact declareRef_lookup_other hxy

theorem declareRef_ctx_old_name_freshness_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr}
    (hneΓ : TypeEnvNonempty Γ)
    (hxy : y ≠ x)
    (hctx : NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p)) :
    currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y := by
  have hΔ : Δ = declareTypeRef Γ x τ := by
    rcases declareRef_post_env_data hctx.hty with
      ⟨_hfresh, _hp, hΔ⟩
    exact hΔ
  subst hΔ
  exact currentTypeScopeFresh_declareRef_other_iff hneΓ hxy

theorem declareRef_ctx_fresh_name_lookup_ref
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    lookupDecl Δ x = some (.ref τ) := by
  intro hctx
  have hΔ : Δ = declareTypeRef Γ x τ := by
    rcases declareRef_post_env_data hctx.hty with
      ⟨_hfresh, _hp, hΔ⟩
    exact hΔ
  subst hΔ
  simp

theorem declareRef_ctx_fresh_name_not_fresh
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr} :
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    ¬ currentTypeScopeFresh Δ x := by
  intro hctx
  have hΔ : Δ = declareTypeRef Γ x τ := by
    rcases declareRef_post_env_data hctx.hty with
      ⟨_hfresh, _hp, hΔ⟩
    exact hΔ
  subst hΔ
  exact currentTypeScopeFresh_declareRef_self_false


/- =========================================================
   3. bundled old-name fragment
   ========================================================= -/

structure ReadinessTransportNormalEnvExtendingOldNameFragment : Type where
  declareObj_lookup_preserved :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x y : Ident} {ov : Option ValExpr},
      y ≠ x →
      NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
      lookupDecl Δ y = lookupDecl Γ y

  declareObj_freshness_preserved :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x y : Ident} {ov : Option ValExpr},
      TypeEnvNonempty Γ →
      y ≠ x →
      NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
      (currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y)

  declareRef_lookup_preserved :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x y : Ident} {p : PlaceExpr},
      y ≠ x →
      NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
      lookupDecl Δ y = lookupDecl Γ y

  declareRef_freshness_preserved :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x y : Ident} {p : PlaceExpr},
      TypeEnvNonempty Γ →
      y ≠ x →
      NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
     ( currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y)


def readinessTransportNormalEnvExtendingOldNameFragment
    : ReadinessTransportNormalEnvExtendingOldNameFragment := by
  refine
    { declareObj_lookup_preserved := by
        intro Γ Δ σ σ' τ x y ov hxy hctx
        exact declareObj_ctx_old_name_lookup_preserved hxy hctx

      declareObj_freshness_preserved := by
        intro Γ Δ σ σ' τ x y ov hneΓ hxy hctx
        exact declareObj_ctx_old_name_freshness_preserved hneΓ hxy hctx

      declareRef_lookup_preserved := by
        intro Γ Δ σ σ' τ x y p hxy hctx
        exact declareRef_ctx_old_name_lookup_preserved hxy hctx

      declareRef_freshness_preserved := by
        intro Γ Δ σ σ' τ x y p hneΓ hxy hctx
        exact declareRef_ctx_old_name_freshness_preserved hneΓ hxy hctx }


/- =========================================================
   4. thin theorem projections
   ========================================================= -/

theorem env_extending_old_name_lookup_preserved_of_declareObj
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    lookupDecl Δ y = lookupDecl Γ y :=
  readinessTransportNormalEnvExtendingOldNameFragment.declareObj_lookup_preserved

theorem env_extending_old_name_freshness_preserved_of_declareObj
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr} :
    TypeEnvNonempty Γ →
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    (currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y) :=
  readinessTransportNormalEnvExtendingOldNameFragment.declareObj_freshness_preserved

theorem env_extending_old_name_lookup_preserved_of_declareRef
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    lookupDecl Δ y = lookupDecl Γ y :=
  readinessTransportNormalEnvExtendingOldNameFragment.declareRef_lookup_preserved

theorem env_extending_old_name_freshness_preserved_of_declareRef
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr} :
    TypeEnvNonempty Γ →
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    (currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y) :=
  readinessTransportNormalEnvExtendingOldNameFragment.declareRef_freshness_preserved

end Cpp
