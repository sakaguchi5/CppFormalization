import CppFormalization.Cpp2.Closure.External.BuilderV3
import CppFormalization.Cpp2.Closure.External.LegacyBridgeV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCoherenceV2

namespace Cpp

/-!
# Closure.External.LegacyBuilderV3

Stage 5: lift the old assumption-style external surface into the builder-based V3 world.

After the adequacy-only refactor of the legacy interface/bridge, each legacy
certificate now also carries:
- an explicit glue object `G : VerifiedExternalGlueLegacy F R`,
- an explicit compatibility witness `hcompat : G.compatible n m Γ σ st`.

The point is still the same:
package the already-used legacy assumption surface into a target-indexed
certificate family so that it lands in the same V3 interfaces as the toy family.
-/

/-- One legacy target certificate, now carrying explicit glue and compatibility. -/
structure LegacyCertificateV3
    (F : VerifiedStdFragment) (R : VerifiedReflectionFragment) where
  G : VerifiedExternalGlueLegacy F R
  n : F.Name
  m : R.Meta
  Γ : TypeEnv
  σ : State
  st : CppStmt
  huse : F.uses n
  hdyn : F.establishesDynamic n Γ σ st
  hgen : R.generates m st
  hstruct : R.establishesStructural m Γ st
  hstatic : R.establishesStatic m Γ st
  hcompat : G.compatible n m Γ σ st

namespace LegacyCertificateV3

/-- The official old assembled closure boundary for this legacy certificate. -/
noncomputable def oldBoundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BodyClosureBoundaryCI c.Γ c.σ c.st :=
  fragments_establish_body_closure_boundary
    c.G c.huse c.hdyn c.hgen c.hstruct c.hstatic c.hcompat

/-- The corresponding old ready witness extracted from the official boundary. -/
noncomputable def oldReady
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BodyReadyCI c.Γ c.σ c.st :=
  (oldBoundary c).toBodyReadyCI

/-- The remaining old core-membership witness. -/
def oldCore
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    CoreBigStepFragment c.st :=
  reflection_fragment_generates_core c.hgen

/-- Explicit V3 pieces obtained from the refactored legacy bridge. -/
noncomputable def oldExternalPieces
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  externalPiecesV3_of_legacy_external_assumptions
    c.G c.huse c.hdyn c.hgen c.hstruct c.hstatic c.hcompat

end LegacyCertificateV3

/-- Builder family generated from the legacy assumption-style surface. -/
noncomputable def legacyCertificateFamilyV3
    (F : VerifiedStdFragment) (R : VerifiedReflectionFragment) :
    ReadyCertificateFamilyV3 where
  Cert := LegacyCertificateV3 F R
  targetΓ := fun c => c.Γ
  targetσ := fun c => c.σ
  targetSt := fun c => c.st
  readyOf := fun c => c.oldReady
  coreOf := fun c => c.oldCore

/-- Builder-generated ready-route pieces for one legacy certificate. -/
noncomputable def legacyReadyExternalPiecesV3
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  (legacyCertificateFamilyV3 F R).readyExternalPieces c

/-- Builder-generated glue-route pieces for one legacy certificate. -/
noncomputable def legacyGlueExternalPiecesV3
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    ExternalPiecesV3 c.Γ c.σ c.st :=
  (legacyCertificateFamilyV3 F R).glueExternalPieces c

theorem legacyReadyExternalPiecesV3_eq_readyExternalPieces
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    legacyReadyExternalPiecesV3 c =
      (legacyCertificateFamilyV3 F R).readyExternalPieces c := by
  rfl

theorem legacyReadyExternalPiecesV3_toBodyBoundary_eq_readyExternalPieces
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyReadyExternalPiecesV3 c).toBodyBoundary =
      ((legacyCertificateFamilyV3 F R).readyExternalPieces c).toBodyBoundary := by
  rw [legacyReadyExternalPiecesV3_eq_readyExternalPieces]

theorem legacyReadyExternalPiecesV3_boundary_eq_ready
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyReadyExternalPiecesV3 c).toBodyBoundary =
      ((legacyCertificateFamilyV3 F R).readyOf c).toClosureBoundary := by
  let B : ReadyCertificateFamilyV3 := legacyCertificateFamilyV3 F R
  rw [legacyReadyExternalPiecesV3_toBodyBoundary_eq_readyExternalPieces]
  simpa [B] using (B.readyExternalPieces_boundary c)

/-- The builder-generated ready route lands on the same official closure boundary
as the original legacy bridge. -/
theorem legacyReadyExternalPiecesV3_boundary_eq_old
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyReadyExternalPiecesV3 c).toBodyBoundary = c.oldBoundary := by
  let B : ReadyCertificateFamilyV3 := legacyCertificateFamilyV3 F R
  calc
    (legacyReadyExternalPiecesV3 c).toBodyBoundary =
        (B.readyOf c).toClosureBoundary := by
      simpa [B] using legacyReadyExternalPiecesV3_boundary_eq_ready c
    _ = c.oldBoundary := by
      simpa [B, legacyCertificateFamilyV3, LegacyCertificateV3.oldReady,
        LegacyCertificateV3.oldBoundary] using
        (bodyClosureBoundaryCI_roundtrip c.oldBoundary)

/-- The builder-generated glue route is boundary-coherent with the builder-generated
ready route on the legacy family. -/
theorem legacy_ready_vs_glue_boundaryCoherent
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BoundaryCoherentV3
      (legacyReadyExternalPiecesV3 c)
      (legacyGlueExternalPiecesV3 c) := by
  let B := legacyCertificateFamilyV3 F R
  simpa [legacyReadyExternalPiecesV3, legacyGlueExternalPiecesV3, B] using
    (B.ready_vs_glue_boundaryCoherent c)

/-- Consequently, the builder-generated glue route lands on the same official
closure boundary as the original legacy bridge as well. -/
theorem legacyGlueExternalPiecesV3_boundary_eq_old
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (legacyGlueExternalPiecesV3 c).toBodyBoundary = c.oldBoundary := by
  calc
    (legacyGlueExternalPiecesV3 c).toBodyBoundary =
        (legacyReadyExternalPiecesV3 c).toBodyBoundary := by
      symm
      exact legacy_ready_vs_glue_boundaryCoherent c
    _ = c.oldBoundary := legacyReadyExternalPiecesV3_boundary_eq_old c

/-- Observable-package level route coherence for the lifted legacy family. -/
theorem legacy_ready_vs_glue_packageCoherent
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    PackageCoherentV3
      (legacyReadyExternalPiecesV3 c).toObservablePieces
      (legacyGlueExternalPiecesV3 c).toObservablePieces := by
  let B := legacyCertificateFamilyV3 F R
  simpa [legacyReadyExternalPiecesV3, legacyGlueExternalPiecesV3, B] using
    (B.ready_vs_glue_packageCoherent c)

/-- The builder-generated ready route gives the expected statement-level closure
result for the lifted legacy family. -/
theorem legacy_ready_certificate_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  let B := legacyCertificateFamilyV3 F R
  simpa [B, legacyCertificateFamilyV3] using (B.ready_certificate_closure c)

/-- The builder-generated glue route gives the expected statement-level closure
result for the lifted legacy family. -/
theorem legacy_glue_certificate_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  let B := legacyCertificateFamilyV3 F R
  simpa [B, legacyCertificateFamilyV3] using (B.glue_certificate_closure c)

/-- Function-body closure through the builder-generated ready route. -/
theorem legacy_ready_certificate_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (∃ ex σ', BigStepFunctionBody c.σ c.st ex σ') ∨ BigStepStmtDiv c.σ c.st := by
  let B := legacyCertificateFamilyV3 F R
  simpa [B, legacyCertificateFamilyV3] using
    (B.ready_certificate_function_body_closure c)

/-- Function-body closure through the builder-generated glue route. -/
theorem legacy_glue_certificate_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (c : LegacyCertificateV3 F R) :
    (∃ ex σ', BigStepFunctionBody c.σ c.st ex σ') ∨ BigStepStmtDiv c.σ c.st := by
  let B := legacyCertificateFamilyV3 F R
  simpa [B, legacyCertificateFamilyV3] using
    (B.glue_certificate_function_body_closure c)

end Cpp
