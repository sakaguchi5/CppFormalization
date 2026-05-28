import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalOldNameLift

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalRefinedAssembly

Stage 8 assembly surface for the refined readiness-transport route.

This is the bridge from the staged refined assets to the full refined surface.
It is not a bridge back to the old unrestricted ` 削除済み`.
That distinction is intentional:

- ` 削除済み` is now a compatibility/debt surface.
- `ReadinessTransportNormalRefinedSurface` is the C++-honest target.
- A full refined surface can be assembled once the Stage-7 old-name
  statement/block fragment is theorem-backed.

No axiom is introduced here.
-/

/- =========================================================
   1. Complete refined fragment
   ========================================================= -/

/--
A complete theorem-backed refined readiness-transport package.

The fresh-name local layer is already theorem-backed by Stage 5.  The only
remaining large theorem family is the old-name statement/block lift supplied by
`oldName`.
-/
structure ReadinessTransportNormalRefinedCompleteFragment : Type where
  knownFresh : ReadinessTransportNormalRefinedKnownAssetsWithFresh
  oldName : ReadinessTransportNormalOldNameStmtBlockFragment

/--
Assemble the full `ReadinessTransportNormalRefinedSurface` from the completed
refined package.

This is the Stage-8 bridge.  It does not touch the old unrestricted core.
-/
def ReadinessTransportNormalRefinedCompleteFragment.toRefinedSurface
    (F : ReadinessTransportNormalRefinedCompleteFragment) :
    ReadinessTransportNormalRefinedSurface :=
  { envPreserving :=
      F.knownFresh.base.base.base.envPreserving

    envExtendingOldNames :=
      F.knownFresh.base.base.base.envExtendingOldNames

    declareObjOldStmtTransport :=
      F.oldName.declareObjOldStmtTransport

    declareObjOldBlockTransport :=
      F.oldName.declareObjOldBlockTransport

    declareRefOldStmtTransport :=
      F.oldName.declareRefOldStmtTransport

    declareRefOldBlockTransport :=
      F.oldName.declareRefOldBlockTransport

    declareObjFreshObjectPlaceIntro :=
      F.knownFresh.base.base.freshIntro.declareObjFreshObjectPlaceIntro

    declareRefFreshPlaceIntro :=
      F.knownFresh.base.base.freshIntro.declareRefFreshPlaceIntro }

/-- Thin projection for users that only need the assembled surface. -/
def refinedSurface_of_completeFragment
    (F : ReadinessTransportNormalRefinedCompleteFragment) :
    ReadinessTransportNormalRefinedSurface :=
  F.toRefinedSurface

end Cpp
