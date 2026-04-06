import CppFormalization.Cpp2.Closure.External.TransportV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap

namespace Cpp

/-!
# Closure.External.ReadyAssemblyV3

Stage 2A redesign:
- the official high-level route still produces `BodyReadyCI`,
- but coherence with runtime/reflection packages is made explicit,
- this lets the visible external pieces be reconstructed from the chosen
  package side, while adequacy is transported from the integrated ready proof.

Stage 2B clarification:
- `PackageCoherentV3` is the strong visible-package comparison notion,
- `BoundaryCoherentV3` remains the official quotient used by the closure theorems.
-/

structure VerifiedExternalReadyAssemblyV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkReady :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      F.uses n →
      F.supportsRuntime n Γ σ st →
      R.generates m st →
      R.supportsReflection m Γ st →
      compatible n m Γ σ st →
      BodyReadyCI Γ σ st

  dynamic_eq :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : F.uses n)
      (hsuppRun : F.supportsRuntime n Γ σ st)
      (hgen : R.generates m st)
      (hsuppRefl : R.supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).toDynamic =
        (F.mkRuntime huse hsuppRun).dynamic

  structural_eq :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : F.uses n)
      (hsuppRun : F.supportsRuntime n Γ σ st)
      (hgen : R.generates m st)
      (hsuppRefl : R.supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).toStructural =
        (R.mkReflection hgen hsuppRefl).structural

  profile_eq :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : F.uses n)
      (hsuppRun : F.supportsRuntime n Γ σ st)
      (hgen : R.generates m st)
      (hsuppRefl : R.supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).toProfile =
        (R.mkReflection hgen hsuppRefl).profile


def externalPieces_of_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  let hr : BodyReadyCI Γ σ st :=
    A.mkReady huse hsuppRun hgen hsuppRefl hcompat
  let hrun : RuntimePiecesV3 Γ σ st := F.mkRuntime huse hsuppRun
  let hrefl : ReflectionPiecesV3 Γ st := R.mkReflection hgen hsuppRefl
  exact
    { structural := hrefl.structural
      profile := hrefl.profile
      dynamic := hrun.dynamic
      core := hrefl.core
      adequacy :=
        transportAdequacy
          (A.profile_eq huse hsuppRun hgen hsuppRefl hcompat)
          hr.toAdequacy }


theorem externalPieces_of_ready_v3_structural
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).structural =
      (R.mkReflection hgen hsuppRefl).structural := by
  rfl


theorem externalPieces_of_ready_v3_profile
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).profile =
      (R.mkReflection hgen hsuppRefl).profile := by
  rfl


theorem externalPieces_of_ready_v3_dynamic
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).dynamic =
      (F.mkRuntime huse hsuppRun).dynamic := by
  rfl


theorem externalPieces_of_ready_v3_adequacy
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).adequacy =
      transportAdequacy
        (A.profile_eq huse hsuppRun hgen hsuppRefl hcompat)
        (A.mkReady huse hsuppRun hgen hsuppRefl hcompat).toAdequacy := by
  rfl


theorem externalPieces_of_ready_v3_packageCoherent
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    PackageCoherentV3
      (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (canonicalVisiblePiecesV3 huse hsuppRun hgen hsuppRefl) := by
  rfl


theorem externalPieces_of_ready_v3_boundary
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary =
      (A.mkReady huse hsuppRun hgen hsuppRefl hcompat).toClosureBoundary := by
  unfold externalPieces_of_ready_v3
  unfold ExternalPiecesV3.toBodyBoundary
  unfold BodyReadyCI.toClosureBoundary
  have hdyn := A.dynamic_eq huse hsuppRun hgen hsuppRefl hcompat
  have hstruct := A.structural_eq huse hsuppRun hgen hsuppRefl hcompat
  have hprof := A.profile_eq huse hsuppRun hgen hsuppRefl hcompat
  cases hdyn
  cases hstruct
  exact mkBodyClosureBoundaryCI_profile_transport hprof _


def assembleBodyBoundary_of_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary


theorem reflective_std_function_body_closure_from_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p := externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      p.core p.toBodyBoundary


theorem reflective_std_closure_theorem_from_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  let p := externalPieces_of_ready_v3 A huse hsuppRun hgen hsuppRefl hcompat
  exact InternalClosureRoadmap.stmt_terminates_or_diverges p.core p.toBodyBoundary

end Cpp
