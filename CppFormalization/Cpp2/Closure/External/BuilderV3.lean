import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3
import CppFormalization.Cpp2.Closure.External.TransportPropsV3

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

This builder is intentionally *not* a canonicity builder. It packages one
certificate family into the V3 interfaces, but it does not claim that two
different certificates with the same target are identical. Family-level
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
      { structural := (B.readyOf c).structural
        static := (B.readyOf c).static
        core := B.coreOf c }


def mkReady_from_compatible
    (B : ReadyCertificateFamilyV3)
    {n : B.toStdFragment.Name} {m : B.toReflectionFragment.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hcompat : n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n) :
    BodyReadyCI Γ σ st := by
  rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
  exact B.readyOf n

theorem compat_dynamic_eq
    (B : ReadyCertificateFamilyV3)
    {n : B.toStdFragment.Name} {m : B.toReflectionFragment.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : B.toStdFragment.uses n)
    (hsuppRun : B.toStdFragment.supportsRuntime n Γ σ st)
    (hgen : B.toReflectionFragment.generates m st)
    (hsuppRefl : B.toReflectionFragment.supportsReflection m Γ st)
    (hcompat : n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n) :
    (mkReady_from_compatible B hcompat).toDynamic =
      (B.toStdFragment.mkRuntime huse hsuppRun).dynamic := by
  rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
  rcases hsuppRun with ⟨_, _, _⟩
  rfl

theorem compat_structural_eq
    (B : ReadyCertificateFamilyV3)
    {n : B.toStdFragment.Name} {m : B.toReflectionFragment.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hgen : B.toReflectionFragment.generates m st)
    (hsuppRefl : B.toReflectionFragment.supportsReflection m Γ st)
    (hcompat : n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n) :
    (mkReady_from_compatible B hcompat).toStructural =
      (B.toReflectionFragment.mkReflection hgen hsuppRefl).structural := by
  rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
  rcases hsuppRefl with ⟨_, _⟩
  rfl

theorem compat_static_eq
    (B : ReadyCertificateFamilyV3)
    {n : B.toStdFragment.Name} {m : B.toReflectionFragment.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hsuppRun : B.toStdFragment.supportsRuntime n Γ σ st)
    (hgen : B.toReflectionFragment.generates m st)
    (hsuppRefl : B.toReflectionFragment.supportsReflection m Γ st)
    (hcompat : n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n) :
    (mkReady_from_compatible B hcompat).static =
      ((B.toReflectionFragment).mkReflection hgen hsuppRefl).static := by
  rcases hcompat with ⟨rfl, rfl, rfl, rfl⟩
  rcases hsuppRefl with ⟨_, _⟩
  unfold ReadyCertificateFamilyV3.toReflectionFragment
  dsimp [mkReady_from_compatible]

/-- The canonical high-level ready assembly generated from the family. -/
def toReadyAssembly (B : ReadyCertificateFamilyV3) :
    VerifiedExternalReadyAssemblyV3 B.toStdFragment B.toReflectionFragment where
  compatible := fun n m Γ σ st =>
    n = m ∧ Γ = B.targetΓ n ∧ σ = B.targetσ n ∧ st = B.targetSt n

  mkReady := fun {_} {_} {_} {_} {_} _ _ _ _ hcompat =>
    mkReady_from_compatible B hcompat

  dynamic_eq := fun huse hsuppRun hgen hsuppRefl hcompat =>
    compat_dynamic_eq B huse hsuppRun hgen hsuppRefl hcompat

  structural_eq := fun _huse _hsuppRun hgen hsuppRefl hcompat =>
    compat_structural_eq B  hgen hsuppRefl hcompat

  static_eq := fun _huse hsuppRun hgen hsuppRefl hcompat =>
    compat_static_eq B hsuppRun hgen hsuppRefl hcompat

def mkAdequacy_from_compatible
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    BodyAdequacyCI Γ σ st ((R.mkReflection hgen hsuppRefl).static.profile) :=
  let hready := A.mkReady huse hsuppRun hgen hsuppRefl hcompat
  castBodyAdequacy
    (congrArg BodyStaticBoundaryCI.profile
      (A.static_eq huse hsuppRun hgen hsuppRefl hcompat))
    hready.toAdequacy

/-- The canonical low-level glue generated from the family. -/
def toGlue
    (B : ReadyCertificateFamilyV3) :
    VerifiedExternalGlueV3 B.toStdFragment B.toReflectionFragment where
  compatible := B.toReadyAssembly.compatible
  mkAdequacy := fun
    {_} {_} {_} {_} {_}
    huse hsuppRun hgen hsuppRefl hcompat =>
      mkAdequacy_from_compatible
        B.toReadyAssembly
        huse hsuppRun hgen hsuppRefl hcompat

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
noncomputable def glueExternalPieces (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    ExternalPiecesV3 (B.targetΓ c) (B.targetσ c) (B.targetSt c) :=
  assembleExternalPiecesV3 B.toGlue
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.glue_compatible_self c)

/-- The ready-route observable package is definitionally the canonical observable package. -/
theorem readyExternalPieces_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.readyExternalPieces c).toObservablePieces
      (canonicalObservablePiecesV3
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

/-- The glue-route observable package agrees with the canonical observable package. -/
theorem glueExternalPieces_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.glueExternalPieces c).toObservablePieces
      (canonicalObservablePiecesV3
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
agree at the observable-package level. -/
theorem ready_vs_glue_packageCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    PackageCoherentV3
      (B.readyExternalPieces c).toObservablePieces
      (B.glueExternalPieces c).toObservablePieces := by
  change (B.readyExternalPieces c).toObservablePieces = (B.glueExternalPieces c).toObservablePieces
  calc
    (B.readyExternalPieces c).toObservablePieces =
        canonicalObservablePiecesV3
          (B.uses_self c)
          (B.supportsRuntime_self c)
          (B.generates_self c)
          (B.supportsReflection_self c) := by
      exact B.readyExternalPieces_packageCoherent c
    _ = (B.glueExternalPieces c).toObservablePieces := by
      symm
      exact B.glueExternalPieces_packageCoherent c

theorem readyAssembly_mkReady_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toReadyAssembly.mkReady
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)
      = B.readyOf c := by
  unfold ReadyCertificateFamilyV3.toReadyAssembly
  unfold mkReady_from_compatible
  rcases B.compatible_self c with ⟨_, _, _, _⟩
  rfl

/-- The ready-route boundary is exactly the certificate boundary. -/
theorem readyExternalPieces_boundary
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readyExternalPieces c).toBodyBoundary =
      (B.readyOf c).toClosureBoundary := by
  have h :=
    externalPieces_of_ready_v3_boundary
      (A := B.toReadyAssembly)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.compatible_self c)
  simpa [ReadyCertificateFamilyV3.readyExternalPieces,
    B.readyAssembly_mkReady_self c] using h

theorem mkReady_from_compatible_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    mkReady_from_compatible B (B.compatible_self c) = B.readyOf c := by
  unfold mkReady_from_compatible
  unfold ReadyCertificateFamilyV3.compatible_self
  simp

/-- Canonical self-profile equality between the certificate ready witness and the
reflection package selected by the builder-generated assembly. -/
theorem readyAssembly_profile_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readyOf c).static.profile =
      (B.toReflectionFragment.mkReflection
        (B.generates_self c)
        (B.supportsReflection_self c)).static.profile := by
  have h :=
    congrArg BodyStaticBoundaryCI.profile
      (compat_static_eq B
        (hsuppRun := B.supportsRuntime_self c)
        (hgen := B.generates_self c)
        (hsuppRefl := B.supportsReflection_self c)
        (hcompat := B.compatible_self c))
  simpa [mkReady_from_compatible_self B c] using h


theorem mkAdequacy_from_compatible_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    mkAdequacy_from_compatible
      B.toReadyAssembly
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)
      =
      (readyAssembly_profile_self B c) ▸ (B.readyOf c).toAdequacy := by
  apply bodyAdequacy_eq


theorem mkAdequacy_from_compatible_self2
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    mkAdequacy_from_compatible
      B.toReadyAssembly
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)
      =
      castBodyAdequacy
        (readyAssembly_profile_self B c)
        ((B.readyOf c).toAdequacy) := by
  rw [castBodyAdequacy_eq_transport]
  -- 2. ターゲットの型を整え、両辺が「依存型における輸送」の形であることを示す
  -- これにより bodyAdequacy_eq が適用可能な状態になります
  apply bodyAdequacy_eq

def readySelf
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    BodyReadyCI (B.targetΓ c) (B.targetσ c) (B.targetSt c) :=
  B.toReadyAssembly.mkReady
    (B.uses_self c)
    (B.supportsRuntime_self c)
    (B.generates_self c)
    (B.supportsReflection_self c)
    (B.compatible_self c)

theorem readySelf_eq
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    readySelf B c = B.readyOf c := by
  exact readyAssembly_mkReady_self B c

theorem readySelf_profile_eq_readyOf
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readyOf c).toProfile = (readySelf B c).toProfile := by
  rw [readySelf_eq]

theorem readySelf_toAdequacy_heq_readyOf
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    HEq (readySelf B c).toAdequacy (B.readyOf c).toAdequacy := by
  rw [readySelf_eq]

theorem readyAssembly_compatible_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.toReadyAssembly.compatible
      c c (B.targetΓ c) (B.targetσ c) (B.targetSt c) := by
  simp [ReadyCertificateFamilyV3.toReadyAssembly]

theorem readyAssembly_static_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readyOf c).static =
      (B.toReflectionFragment.mkReflection
        (B.generates_self c)
        (B.supportsReflection_self c)).static := by
  have h :=
    B.toReadyAssembly.static_eq
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (readyAssembly_compatible_self B c)
  simpa [readyAssembly_mkReady_self B c] using h


theorem mkAdequacy_from_compatible_eq_cast
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    mkAdequacy_from_compatible A huse hsuppRun hgen hsuppRefl hcompat
      =
    castBodyAdequacy
      (congrArg BodyStaticBoundaryCI.profile
        (A.static_eq huse hsuppRun hgen hsuppRefl hcompat))
      ((A.mkReady huse hsuppRun hgen hsuppRefl hcompat).toAdequacy) := by
  unfold mkAdequacy_from_compatible
  simp

theorem mkAdequacy_from_compatible_cast
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {ready : BodyReadyCI Γ σ st}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st)
    (hready : A.mkReady huse hsuppRun hgen hsuppRefl hcompat = ready)
    (hstatic : ready.toStatic = (R.mkReflection hgen hsuppRefl).static) :
    castBodyAdequacy
      (Eq.symm (congrArg BodyStaticBoundaryCI.profile hstatic))
      (mkAdequacy_from_compatible A huse hsuppRun hgen hsuppRefl hcompat)
      =
      ready.toAdequacy := by
  subst ready
  rw [mkAdequacy_from_compatible_eq_cast]
  have hprof :
      congrArg BodyStaticBoundaryCI.profile
        (A.static_eq huse hsuppRun hgen hsuppRefl hcompat)
      =
      congrArg BodyStaticBoundaryCI.profile hstatic := by
    apply Subsingleton.elim
  rw [hprof]
  simpa using
    (castBodyAdequacy_symm
      ((A.mkReady huse hsuppRun hgen hsuppRefl hcompat).toAdequacy)
      (congrArg BodyStaticBoundaryCI.profile hstatic))



/-- On the canonical self-input, the family glue adequacy is the certificate adequacy
transported along the canonical self profile equality. -/
theorem glue_mkAdequacy_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    castBodyAdequacy
      (Eq.symm (readyAssembly_profile_self B c))
      (B.toGlue.mkAdequacy
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)
        (B.glue_compatible_self c))
      =
      (B.readyOf c).toAdequacy := by
  have hcompat := readyAssembly_compatible_self B c
  have hready := readyAssembly_mkReady_self B c
  have hstatic := readyAssembly_static_self B c
  simpa [ReadyCertificateFamilyV3.readyAssembly_profile_self,
    ReadyCertificateFamilyV3.toGlue] using
    (mkAdequacy_from_compatible_cast
      (A := B.toReadyAssembly)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := hcompat)
      (ready := B.readyOf c)
      hready hstatic)

theorem readyAssembly_dynamic_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readySelf c).toDynamic =
      (B.toStdFragment.mkRuntime
        (B.uses_self c)
        (B.supportsRuntime_self c)).dynamic := by
  exact
    B.toReadyAssembly.dynamic_eq
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)

theorem readyAssembly_structural_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readySelf c).toStructural =
      (B.toReflectionFragment.mkReflection
        (B.generates_self c)
        (B.supportsReflection_self c)).structural := by
  exact
    B.toReadyAssembly.structural_eq
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)

theorem readySelf_profile_self
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.readySelf c).toProfile =
      (B.toReflectionFragment.mkReflection
        (B.generates_self c)
        (B.supportsReflection_self c)).profile := by
  exact
    B.toReadyAssembly.profile_eq
      (B.uses_self c)
      (B.supportsRuntime_self c)
      (B.generates_self c)
      (B.supportsReflection_self c)
      (B.compatible_self c)

theorem glueExternalPieces_eq_assemble
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    B.glueExternalPieces c =
      assembleExternalPiecesV3
        B.toGlue
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)
        (B.glue_compatible_self c) := by
  rfl

theorem glueExternalPieces_toBodyBoundary_eq_assemble
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.glueExternalPieces c).toBodyBoundary =
      (assembleExternalPiecesV3
        B.toGlue
        (B.uses_self c)
        (B.supportsRuntime_self c)
        (B.generates_self c)
        (B.supportsReflection_self c)
        (B.glue_compatible_self c)).toBodyBoundary := by
  rw [glueExternalPieces_eq_assemble B c]

theorem glueExternalPieces_toBodyBoundary_expand
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.glueExternalPieces c).toBodyBoundary =
      mkBodyClosureBoundaryCI
        ((B.toReflectionFragment.mkReflection
          (B.generates_self c)
          (B.supportsReflection_self c)).structural)
        ((B.toReflectionFragment.mkReflection
          (B.generates_self c)
          (B.supportsReflection_self c)).static)
        ((B.toStdFragment.mkRuntime
          (B.uses_self c)
          (B.supportsRuntime_self c)).dynamic)
        (B.toGlue.mkAdequacy
          (B.uses_self c)
          (B.supportsRuntime_self c)
          (B.generates_self c)
          (B.supportsReflection_self c)
          (B.glue_compatible_self c)) := by
  rw [glueExternalPieces_toBodyBoundary_eq_assemble B c]
  exact
    assembleExternalPiecesV3_toBodyBoundary
      (G := B.toGlue)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.glue_compatible_self c)
/--
Glue ルートで組み立てた外部境界が、証明書 `c` から得られる closure 境界と一致することを示す。

ここでの一致は、
- profile 成分については通常の等式
- adequacy 成分については profile 等式に沿った依存型の transport を含む一致
として示される。
-/
theorem glueExternalPieces_boundary
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    (B.glueExternalPieces c).toBodyBoundary =
      (B.readyOf c).toClosureBoundary := by
  rw [glueExternalPieces_toBodyBoundary_expand]
  unfold BodyReadyCI.toClosureBoundary
  ext
  · -- structural
    simp
  · -- static
    change
      (B.toReflectionFragment.mkReflection
      (B.generates_self c)
      (B.supportsReflection_self c)).static
        =
      (B.readyOf c).static
    cases B with
      | mk Cert targetΓ targetσ targetSt readyOf coreOf =>
        -- 1. ReflectionFragment の定義を展開
        simp [ReadyCertificateFamilyV3.toReflectionFragment]
        -- 2. ここが肝：mkReflection の引数に使われている証明の定義を展開する
        -- これにより And.rec の対象が具体的な ⟨rfl, rfl⟩ の形に見えるようになる
        unfold ReadyCertificateFamilyV3.supportsReflection_self
        dsimp
  · -- dynamic
    simp
  · -- adequacy
    simpa using glue_mkAdequacy_self B c


/-- For a builder-generated family, the direct ready route and the direct glue route
also agree at the official boundary quotient. -/
theorem ready_vs_glue_boundaryCoherent
    (B : ReadyCertificateFamilyV3) (c : B.Cert) :
    BoundaryCoherentV3
      (B.readyExternalPieces c)
      (B.glueExternalPieces c) := by
  change (B.readyExternalPieces c).toBodyBoundary =
    (B.glueExternalPieces c).toBodyBoundary
  calc
    (B.readyExternalPieces c).toBodyBoundary =
        (B.readyOf c).toClosureBoundary := by
      exact B.readyExternalPieces_boundary c
    _ = (B.glueExternalPieces c).toBodyBoundary := by
      symm
      exact B.glueExternalPieces_boundary c

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
        (B.glue_compatible_self c)).toObservablePieces
      (B.glueExternalPieces c).toObservablePieces := by
  simpa [glueExternalPieces] using
    (externalPieces_of_ready_from_glue_v3_packageCoherent
      (G := B.toGlue)
      (huse := B.uses_self c)
      (hsuppRun := B.supportsRuntime_self c)
      (hgen := B.generates_self c)
      (hsuppRefl := B.supportsReflection_self c)
      (hcompat := B.glue_compatible_self c))

/-- The ready route generated from the low-level glue is boundary-coherent with the
family's direct glue route. This is the official comparison notion used by the
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
