import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3

namespace Cpp

/-!
# Closure.External.BuilderV3

Stage 4 builder layer.

The purpose of this file is to stop repeating the same first-family pattern:
from a target-indexed certificate carrying
- a ready witness, and
- a core witness,
construct automatically
- the runtime/std fragment,
- the reflection fragment,
- the high-level ready assembly,
- the low-level glue assembly,
- and the basic route-level corollaries for the concrete family.

This builder is intentionally *not* a canonicity builder.  It packages one
certificate family into the V3 interfaces, but it does not claim that two
different certificates with the same target are identical.  Family-level
canonicity remains a separate Stage 2C notion.
-/

structure ReadyCertificateFamilyV3 where
  Cert : Type
  targetΓ : Cert → TypeEnv
  targetσ : Cert → State
  targetSt : Cert → CppStmt
  readyOf : (c : Cert) → BodyReadyCI (targetΓ c) (targetσ c) (targetSt c)
  coreOf : (c : Cert) → CoreBigStepFragment (targetSt c)

namespace ReadyCertificateFamilyV3

/-- Runtime-side V3 fragment generated from a ready-certificate family. -/
def toStdFragment (B : ReadyCertificateFamilyV3) : VerifiedStdFragmentV3 where
  Name := B.Cert
  uses := fun _ => True
  supportsRuntime := fun c Γ σ st =>
    Γ = B.targetΓ c ∧ σ = B.targetσ c ∧ st = B.targetSt c
  mkRuntime := by
    intro c Γ σ st _ hsupp
    rcases hsupp with ⟨rfl, rfl, rfl⟩
    exact { dynamic := (B.readyOf c).toDynamic }

/-- Reflection-side V3 fragment generated from a ready-certificate family. -/
def toReflectionFragment (B : ReadyCertificateFamilyV3) : VerifiedReflectionFragmentV3 where
  Meta := B.Cert
  generates := fun c st => st = B.targetSt c
  supportsReflection := fun c Γ st =>
    Γ = B.targetΓ c ∧ st = B.targetSt c
  mkReflection := by
    intro c Γ st _ hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    exact
      { structural := (B.readyOf c).toStructural
        profile := (B.readyOf c).toProfile
        core := B.coreOf c }

/-- The canonical high-level ready assembly generated from the family. -/
def toReadyAssembly
    (B : ReadyCertificateFamilyV3) :
    VerifiedExternalReadyAssemblyV3 B.toStdFragment B.toReflectionFragment where
  compatible := fun n m Γ σ st =>
    n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n
  mkReady := by
    intro n m Γ σ st _ _ _ _ hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    exact B.readyOf n
  dynamic_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRun with ⟨_, _, _⟩
    rfl
  structural_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    rfl
  profile_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    rfl

/-- The canonical low-level glue generated from the family. -/
def toGlue
    (B : ReadyCertificateFamilyV3) :
    VerifiedExternalGlueV3 B.toStdFragment B.toReflectionFragment where
  compatible := (B.toReadyAssembly).compatible
  mkAdequacy := by
    intro n m Γ σ st _ _ hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    simpa [toReflectionFragment] using (B.readyOf n).toAdequacy

/-- Canonical self-use witness for a family certificate. -/
theorem uses_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toStdFragment.uses c := by
  trivial

/-- Canonical runtime-support witness for a family certificate. -/
theorem supportsRuntime_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toStdFragment.supportsRuntime c (B.targetΓ c) (B.targetσ c) (B.targetSt c) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical generate witness for a family certificate. -/
theorem generates_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toReflectionFragment.generates c (B.targetSt c) := by
  rfl

/-- Canonical reflection-support witness for a family certificate. -/
theorem supportsReflection_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toReflectionFragment.supportsReflection c (B.targetΓ c) (B.targetSt c) := by
  exact ⟨rfl, rfl⟩

/-- Canonical ready-route compatibility witness for a family certificate. -/
theorem compatible_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toReadyAssembly.compatible c c (B.targetΓ c) (B.targetσ c) (B.targetSt c) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Canonical glue-route compatibility witness for a family certificate. -/
theorem glue_compatible_self (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toGlue.compatible c c (B.targetΓ c) (B.targetσ c) (B.targetSt c) := by
  exact B.compatible_self c

/-- Canonical explicit V3 pieces from the ready route for a family certificate. -/
def readyExternalPieces (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    ExternalPiecesV3 (B.targetΓ c) (B.targetσ c) (B.targetSt c) :=
  externalPieces_of_ready_v3 B.toReadyAssembly
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.compatible_self c)

/-- Canonical explicit V3 pieces from the low-level glue route for a family certificate. -/
def glueExternalPieces (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    ExternalPiecesV3 (B.targetΓ c) (B.targetσ c) (B.targetSt c) :=
  assembleExternalPiecesV3 B.toGlue
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.glue_compatible_self c)

/-- The ready-route visible package is definitionally the canonical visible package. -/
theorem readyExternalPieces_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.readyExternalPieces c).toVisiblePieces
      (canonicalVisiblePiecesV3
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)) := by
  simpa [readyExternalPieces] using
    (externalPieces_of_ready_v3_packageCoherent
      (A := B.toReadyAssembly)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.compatible_self c))

/-- The glue-route visible package agrees with the canonical visible package. -/
theorem glueExternalPieces_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.glueExternalPieces c).toVisiblePieces
      (canonicalVisiblePiecesV3
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)) := by
  simpa [glueExternalPieces] using
    (assembleExternalPiecesV3_packageCoherent
      (G := B.toGlue)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.glue_compatible_self c))

/-- Within a builder-generated family, the direct ready route and direct glue route
agree at the visible-package level. -/
theorem ready_vs_glue_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.readyExternalPieces c).toVisiblePieces
      (B.glueExternalPieces c).toVisiblePieces := by
  change (B.readyExternalPieces c).toVisiblePieces = (B.glueExternalPieces c).toVisiblePieces
  calc
    (B.readyExternalPieces c).toVisiblePieces =
        canonicalVisiblePiecesV3
          (B.uses_self c)
          (B.supportsRuntime_self c)
          (B.generates_self c)
          (B.supportsReflection_self c) := by
      exact B.readyExternalPieces_packageCoherent c
    _ = (B.glueExternalPieces c).toVisiblePieces := by
      symm
      exact B.glueExternalPieces_packageCoherent c

/-- The ready route generated from the low-level glue is package-coherent with the
family's direct glue route. -/
theorem glue_readyInduced_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 B.toGlue)
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)
        (B.glue_compatible_self c)).toVisiblePieces
      (B.glueExternalPieces c).toVisiblePieces := by
  simpa [glueExternalPieces] using
    (externalPieces_of_ready_from_glue_v3_packageCoherent
      (G := B.toGlue)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.glue_compatible_self c))

/-- The ready route generated from the low-level glue is boundary-coherent with the
family's direct glue route.  This is the official comparison notion used by the
closure theorems. -/
theorem glue_readyInduced_boundaryCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    BoundaryCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 B.toGlue)
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)
        (B.glue_compatible_self c))
      (B.glueExternalPieces c) := by
  simpa [glueExternalPieces] using
    (externalPieces_of_ready_from_glue_v3_boundaryCoherent
      (G := B.toGlue)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.glue_compatible_self c))

/-- Statement-level closure theorem through the family-generated ready route. -/
theorem ready_certificate_closure
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    BigStepStmtTerminates (B.targetσ c) (B.targetSt c) ∨
      BigStepStmtDiv (B.targetσ c) (B.targetSt c) := by
  exact reflective_std_closure_theorem_from_ready_v3
    B.toReadyAssembly
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.compatible_self c)

/-- Function-body closure theorem through the family-generated ready route. -/
theorem ready_certificate_function_body_closure
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (∃ ex σ', BigStepFunctionBody (B.targetσ c) (B.targetSt c) ex σ') ∨
      BigStepStmtDiv (B.targetσ c) (B.targetSt c) := by
  exact reflective_std_function_body_closure_from_ready_v3
    B.toReadyAssembly
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.compatible_self c)

/-- Statement-level closure theorem through the family-generated low-level glue route. -/
theorem glue_certificate_closure
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    BigStepStmtTerminates (B.targetσ c) (B.targetSt c) ∨
      BigStepStmtDiv (B.targetσ c) (B.targetSt c) := by
  exact reflective_std_closure_theorem_v3_via_ready
    B.toGlue
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.glue_compatible_self c)

/-- Function-body closure theorem through the family-generated low-level glue route. -/
theorem glue_certificate_function_body_closure
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (∃ ex σ', BigStepFunctionBody (B.targetσ c) (B.targetSt c) ex σ') ∨
      BigStepStmtDiv (B.targetσ c) (B.targetSt c) := by
  exact reflective_std_function_body_closure_v3_via_ready
    B.toGlue
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.glue_compatible_self c)

end ReadyCertificateFamilyV3

end Cpp
