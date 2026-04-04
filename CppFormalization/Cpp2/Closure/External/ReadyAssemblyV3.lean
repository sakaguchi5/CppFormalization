import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap

namespace Cpp

/-!
# Closure.External.ReadyAssemblyV3

A stronger target-indexed external assembly route.

Compared with V2:
- the fragment-side applicability conditions are made explicit again,
- integrated assembly is still exposed via a single `BodyReadyCI`,
- the final target remains the same official mainline object
  `BodyClosureBoundaryCI`.

New in this file:
- adequacy transport is generalized here rather than left inside toy instances,
- generic comparison lemmas explain how `externalPieces_of_ready_v3` relates to
  the underlying `mkReady` witness.
-/

structure VerifiedExternalReadyAssemblyV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkReady :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      F.uses n →
      F.supportsDynamic n Γ σ st →
      R.generates m st →
      R.supportsStructural m Γ st →
      R.supportsProfile m Γ st →
      compatible n m Γ σ st →
      BodyReadyCI Γ σ st

/-- Transport adequacy across propositional equality of control profiles. -/
def transportAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p q : BodyControlProfile Γ st}
    (h : p = q) :
    BodyAdequacyCI Γ σ st p → BodyAdequacyCI Γ σ st q := by
  intro ha
  cases h
  exact ha

@[simp] theorem transportAdequacy_rfl
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (ha : BodyAdequacyCI Γ σ st p) :
    transportAdequacy rfl ha = ha := by
  rfl

def externalPieces_of_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  let hr : BodyReadyCI Γ σ st :=
    A.mkReady huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  let hc : CoreBigStepFragment st := R.mkCore hgen
  exact
    { structural := hr.toStructural
      profile := hr.toProfile
      dynamic := hr.toDynamic
      core := hc
      adequacy := hr.toAdequacy }

/-- Generic profile comparison for the ready-route reconstruction. -/
theorem externalPieces_of_ready_v3_profile
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).profile
      =
    (A.mkReady huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toProfile := by
  rfl

/--
Generic adequacy comparison for the ready-route reconstruction.

This is the abstract version of the issue first discovered in the toy instance:
`adequacy` is dependent on `profile`, so one generally needs transport along the
profile equality when comparing the reconstructed pieces with the original
integrated witness.
-/
theorem externalPieces_of_ready_v3_adequacy
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    transportAdequacy
      (externalPieces_of_ready_v3_profile A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).symm
      (A.mkReady huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toAdequacy
      =
    (externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).adequacy := by
  unfold externalPieces_of_ready_v3 externalPieces_of_ready_v3_profile transportAdequacy
  rfl

/-- The assembled boundary reconstructed from a ready witness is the expected one. -/
theorem externalPieces_of_ready_v3_boundary
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toBodyBoundary
      =
    (A.mkReady huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toClosureBoundary := by
  rfl

def assembleBodyBoundary_of_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toBodyBoundary

theorem reflective_std_function_body_closure_from_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsDynamic n Γ σ st →
    R.generates m st →
    R.supportsStructural m Γ st →
    R.supportsProfile m Γ st →
    A.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  let p := externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      p.core
      p.toBodyBoundary

theorem reflective_std_closure_theorem_from_ready_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (A : VerifiedExternalReadyAssemblyV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsDynamic n Γ σ st →
    R.generates m st →
    R.supportsStructural m Γ st →
    R.supportsProfile m Γ st →
    A.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  let p := externalPieces_of_ready_v3 A huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core
      p.toBodyBoundary

end Cpp
