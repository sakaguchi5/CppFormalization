import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalFreshExpr

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalOldNameTransport

Stage 6 surface for the refined readiness-transport route.

This file is intentionally conservative.  Old-name transport for env-extending
heads is the first genuinely hard part after the fresh-name local layer.

The important design point is that this file does **not** reintroduce the old
unrestricted ` 削除済み` claim.  It records only the C++-honest
old-name transport targets:

- the transported target must syntactically avoid the freshly introduced name;
- fresh names are handled by the fresh-introduction files, not by transport;
- load/read readiness remains guarded by the explicit read-condition discipline
  already isolated in `ReadinessTransportNormalFreshRead`.

No axiom is introduced here.  The structures below are theorem-family surfaces
that later files can instantiate once the recursive old-name proofs are built.
-/

/- =========================================================
   1. Stage-6 place/expression old-name transport surface
   ========================================================= -/

/--
The place/expression part of env-extending old-name transport.

These are the true Stage-6 targets.  They are deliberately split by declaration
kind so later proofs can use the declaration-specific lookup algebra already
available from `ReadinessTransportNormalEnvExtendingOldNames`.
-/
structure ReadinessTransportNormalOldNamePlaceExprFragment : Type where
  declareObjOldPlaceTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      EnvExtendingOldNamePlaceTransportGoal
        Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) x

  declareObjOldExprTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      EnvExtendingOldNameExprTransportGoal
        Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) x

  declareRefOldPlaceTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      EnvExtendingOldNamePlaceTransportGoal
        Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) x

  declareRefOldExprTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      EnvExtendingOldNameExprTransportGoal
        Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) x

/--
Known refined assets plus the still-future Stage-6 old-name place/expression
fragment.

This does not instantiate anything by itself; it is a typed checkpoint making
the remaining obligation explicit.
-/
structure ReadinessTransportNormalKnownWithOldNamePlaceExpr : Type where
  knownFresh : ReadinessTransportNormalRefinedKnownAssetsWithFresh
  oldNamePlaceExpr : ReadinessTransportNormalOldNamePlaceExprFragment

end Cpp
