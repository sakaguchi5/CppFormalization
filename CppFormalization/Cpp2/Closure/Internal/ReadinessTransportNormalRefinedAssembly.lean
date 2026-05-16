import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalOldNameLift

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalRefinedAssembly

Stage 8 assembly surface for the refined readiness-transport route.

This is the bridge from the staged refined assets to the full refined surface.
It is not a bridge back to the old unrestricted `ReadinessTransportNormalCore`.
That distinction is intentional:

- `ReadinessTransportNormalCore` is now a compatibility/debt surface.
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

/- =========================================================
   2. Stage-8 replacement boundary
   ========================================================= -/

/--
A named boundary for the future replacement of the old general transport debt.

This deliberately stores a refined surface, not `ReadinessTransportNormalCore`.
The old core is too coarse as a final theorem target; replacement means moving
callers to refined obligations, not proving the unrestricted core verbatim.
-/
structure ReadinessTransportNormalCoreReplacementBoundary : Type where
  refined : ReadinessTransportNormalRefinedSurface

/-- Build the replacement boundary from a complete refined fragment. -/
def coreReplacementBoundary_of_completeFragment
    (F : ReadinessTransportNormalRefinedCompleteFragment) :
    ReadinessTransportNormalCoreReplacementBoundary :=
  { refined := F.toRefinedSurface }

end Cpp
