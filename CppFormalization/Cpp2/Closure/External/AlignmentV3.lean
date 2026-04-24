import CppFormalization.Cpp2.Closure.External.ToyBuilderV3
import CppFormalization.Cpp2.Closure.External.LegacyBuilderV3

namespace Cpp

/-!
# Closure.External.AlignmentV3

Stage 6 canonical-surface alignment lemmas.

Purpose:
- record that the builder-generated toy routes land on the same official quotient
  as the earlier hand-written toy routes,
- record that the builder-generated legacy routes land on the same official quotient
  as the earlier direct legacy bridge,
- let the V3 surface be treated as canonical without discarding the earlier
  development history.
-/

section ToyAlignment

theorem toy_builder_ready_boundary_eq_handwritten
    (c : ToyReadyCertificate) :
    (toyCertificateFamilyV3.readyExternalPieces c).toBodyBoundary =
      (toyExternalPiecesV3 c).toBodyBoundary := by
  calc
    (toyCertificateFamilyV3.readyExternalPieces c).toBodyBoundary
        = c.ready.toClosureBoundary := by
            simpa [toyCertificateFamilyV3] using
              (toyCertificateFamilyV3.readyExternalPieces_boundary c)
    _ = (toyExternalPiecesV3 c).toBodyBoundary := by
          symm
          exact toyExternalPiecesV3_boundary c

theorem toy_builder_ready_boundaryCoherent_handwritten
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (toyCertificateFamilyV3.readyExternalPieces c)
      (toyExternalPiecesV3 c) := by
  exact toy_builder_ready_boundary_eq_handwritten c

theorem toy_builder_glue_boundary_eq_handwritten
    (c : ToyReadyCertificate) :
    (toyCertificateFamilyV3.glueExternalPieces c).toBodyBoundary =
      (toyGlueExternalPiecesV3 c).toBodyBoundary := by
  calc
    (toyCertificateFamilyV3.glueExternalPieces c).toBodyBoundary
        = c.ready.toClosureBoundary := by
            simpa [toyCertificateFamilyV3] using
              (toyCertificateFamilyV3.glueExternalPieces_boundary c)
    _ = (toyGlueExternalPiecesV3 c).toBodyBoundary := by
          symm
          exact toyGlueExternalPiecesV3_boundary c

theorem toy_builder_glue_boundaryCoherent_handwritten
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (toyCertificateFamilyV3.glueExternalPieces c)
      (toyGlueExternalPiecesV3 c) := by
  exact toy_builder_glue_boundary_eq_handwritten c

end ToyAlignment

section LegacyAlignment

theorem legacy_builder_ready_boundary_eq_bridge
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyReadyExternalPiecesV3 c).toBodyBoundary =
      (c.oldExternalPieces).toBodyBoundary := by
  calc
    (legacyReadyExternalPiecesV3 c).toBodyBoundary
        = c.oldBoundary := by
            exact legacyReadyExternalPiecesV3_boundary_eq_old c
    _ = (c.oldExternalPieces).toBodyBoundary := by
          symm
          exact
            externalPiecesV3_of_legacy_external_assumptions_boundary
              c.G c.huse c.hdyn c.hgen c.hstruct c.hstatic c.hcompat

theorem legacy_builder_ready_boundaryCoherent_bridge
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BoundaryCoherentV3
      (legacyReadyExternalPiecesV3 c)
      (c.oldExternalPieces) := by
  exact legacy_builder_ready_boundary_eq_bridge c

theorem legacy_builder_glue_boundary_eq_bridge
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyGlueExternalPiecesV3 c).toBodyBoundary =
      (c.oldExternalPieces).toBodyBoundary := by
  calc
    (legacyGlueExternalPiecesV3 c).toBodyBoundary
        = c.oldBoundary := by
            exact legacyGlueExternalPiecesV3_boundary_eq_old c
    _ = (c.oldExternalPieces).toBodyBoundary := by
          symm
          exact
            externalPiecesV3_of_legacy_external_assumptions_boundary
              c.G c.huse c.hdyn c.hgen c.hstruct c.hstatic c.hcompat

theorem legacy_builder_glue_boundaryCoherent_bridge
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BoundaryCoherentV3
      (legacyGlueExternalPiecesV3 c)
      (c.oldExternalPieces) := by
  exact legacy_builder_glue_boundary_eq_bridge c

end LegacyAlignment

end Cpp
