import CppFormalization.Cpp2.Closure.External.BuilderV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3
import CppFormalization.Cpp2.Closure.External.ToyGlueInstanceV3

namespace Cpp

/-!
# Closure.External.ToyBuilderV3

First concrete consumer of the Stage 4 builder layer.

This file does not replace the hand-written toy files immediately.  Its role is
more conservative:
- package the existing `ToyReadyCertificate` world as a builder family,
- expose the builder-generated routes,
- and record the intended alignment with the existing toy route vocabulary.
-/

def toyCertificateFamilyV3 : ReadyCertificateFamilyV3 where
  Cert := ToyReadyCertificate
  targetΓ := ToyReadyCertificate.Γ
  targetσ := ToyReadyCertificate.σ
  targetSt := ToyReadyCertificate.st
  readyOf := ToyReadyCertificate.ready
  coreOf := ToyReadyCertificate.core

abbrev toyStdFragmentV3_built : VerifiedStdFragmentV3 :=
  toyCertificateFamilyV3.toStdFragment

abbrev toyReflectionFragmentV3_built : VerifiedReflectionFragmentV3 :=
  toyCertificateFamilyV3.toReflectionFragment

abbrev toyReadyAssemblyV3_built :
    VerifiedExternalReadyAssemblyV3 toyStdFragmentV3_built toyReflectionFragmentV3_built :=
  toyCertificateFamilyV3.toReadyAssembly

abbrev toyGlueV3_built :
    VerifiedExternalGlueV3 toyStdFragmentV3_built toyReflectionFragmentV3_built :=
  toyCertificateFamilyV3.toGlue

/-- The builder-generated toy ready route carries the same closure content. -/
theorem toy_builder_ready_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  simpa [toyCertificateFamilyV3] using
    (toyCertificateFamilyV3.ready_certificate_closure c)

/-- The builder-generated toy glue route carries the same closure content. -/
theorem toy_builder_glue_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  simpa [toyCertificateFamilyV3] using
    (toyCertificateFamilyV3.glue_certificate_closure c)

/-- The builder-generated toy ready/glue routes agree at the visible-package level. -/
theorem toy_builder_ready_vs_glue_packageCoherent
    (c : ToyReadyCertificate) :
    PackageCoherentV3
      (toyCertificateFamilyV3.readyExternalPieces c).toObservablePieces
      (toyCertificateFamilyV3.glueExternalPieces c).toObservablePieces := by
  simpa [toyCertificateFamilyV3] using
    (toyCertificateFamilyV3.ready_vs_glue_packageCoherent c)

/-- The builder-generated toy glue-induced ready route is boundary-coherent with
its direct glue route. -/
theorem toy_builder_glue_readyInduced_boundaryCoherent
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 toyGlueV3_built)
        (toyCertificateFamilyV3.uses_self c)
        (toyCertificateFamilyV3.supportsRuntime_self c)
        (toyCertificateFamilyV3.generates_self c)
        (toyCertificateFamilyV3.supportsReflection_self c)
        (toyCertificateFamilyV3.glue_compatible_self c))
      (toyCertificateFamilyV3.glueExternalPieces c) := by
  simpa [toyCertificateFamilyV3, toyGlueV3_built] using
    (toyCertificateFamilyV3.glue_readyInduced_boundaryCoherent c)

end Cpp
