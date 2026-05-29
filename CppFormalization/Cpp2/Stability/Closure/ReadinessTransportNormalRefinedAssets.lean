import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalRefined

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalRefinedAssets

Known theorem-backed assets for the refined readiness-transport route.

`ReadinessTransportNormalRefined.lean` introduces the future refined surface, but
that full surface still contains obligations that are not theorem-backed yet
(old-name statement/block transport and fresh-name introduction).

This file intentionally does **not** instantiate the full refined surface.
Instead, it records the parts that are already theorem-backed:
- replay-stable / env-preserving transport fragment;
- env-preserving wrapper fragment;
- env-extending old-name lookup/freshness fragment.

This gives the next stages a clean distinction between known assets and future
obligations.
-/

/--
The already-theorem-backed portion of the refined readiness-transport program.

This is deliberately smaller than `ReadinessTransportNormalRefinedSurface`.
It contains only assets that already exist as definitions/proofs.
-/
structure ReadinessTransportNormalRefinedKnownAssets : Type where
  stable : ReadinessTransportNormalStableFragment
  envPreserving : ReadinessTransportNormalEnvPreservingFragment
  envExtendingOldNames : ReadinessTransportNormalEnvExtendingOldNameFragment

/--
Current known-assets registry for the refined route.
-/
def readinessTransportNormalRefinedKnownAssets :
    ReadinessTransportNormalRefinedKnownAssets :=
  { stable := readinessTransportNormalStableFragment
    envPreserving := readinessTransportNormalEnvPreservingFragment
    envExtendingOldNames := readinessTransportNormalEnvExtendingOldNameFragment }

/- =========================================================
   Thin projections
   ========================================================= -/

/-- The theorem-backed replay-stable primitive fragment. -/
def refinedKnown_stableFragment : ReadinessTransportNormalStableFragment :=
  readinessTransportNormalRefinedKnownAssets.stable

/-- The theorem-backed env-preserving wrapper fragment. -/
def refinedKnown_envPreservingFragment :
    ReadinessTransportNormalEnvPreservingFragment :=
  readinessTransportNormalRefinedKnownAssets.envPreserving

/-- The theorem-backed env-extending old-name lookup/freshness fragment. -/
def refinedKnown_envExtendingOldNameFragment :
    ReadinessTransportNormalEnvExtendingOldNameFragment :=
  readinessTransportNormalRefinedKnownAssets.envExtendingOldNames

/- =========================================================
   Small named corollaries for later stages
   ========================================================= -/

/-- Env-preserving heads keep the post type environment equal to the pre one. -/
theorem refinedKnown_env_preserving_same_env
    {Γ Δ : TypeEnv} {head : CppStmt} :
    EnvPreservingNormalHead head →
    HasTypeStmtCI .normalK Γ head Δ →
    Δ = Γ :=
  refinedKnown_envPreservingFragment.sameEnv

/-- Old object-declaration names have the same lookup after the declaration. -/
theorem refinedKnown_declareObj_old_name_lookup_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    lookupDecl Δ y = lookupDecl Γ y :=
  refinedKnown_envExtendingOldNameFragment.declareObj_lookup_preserved

/-- Old reference-declaration names have the same lookup after the declaration. -/
theorem refinedKnown_declareRef_old_name_lookup_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr} :
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    lookupDecl Δ y = lookupDecl Γ y :=
  refinedKnown_envExtendingOldNameFragment.declareRef_lookup_preserved

/-- Freshness for old object-declaration names is preserved across the declaration. -/
theorem refinedKnown_declareObj_old_name_freshness_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {ov : Option ValExpr} :
    TypeEnvNonempty Γ →
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareObj τ x ov) →
    (currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y) :=
  refinedKnown_envExtendingOldNameFragment.declareObj_freshness_preserved

/-- Freshness for old reference-declaration names is preserved across the declaration. -/
theorem refinedKnown_declareRef_old_name_freshness_preserved
    {Γ Δ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x y : Ident} {p : PlaceExpr} :
    TypeEnvNonempty Γ →
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' (.declareRef τ x p) →
    (currentTypeScopeFresh Δ y ↔ currentTypeScopeFresh Γ y) :=
  refinedKnown_envExtendingOldNameFragment.declareRef_freshness_preserved

end Cpp
