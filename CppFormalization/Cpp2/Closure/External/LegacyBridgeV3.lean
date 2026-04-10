import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.LegacyBridgeV3

Bridge the old external assumption-style interface into the target-indexed V3
assembly object `ExternalPiecesV3`.

After the adequacy-only refactor of `Interface.lean`, the legacy bridge now
threads:
- an explicit glue object `G : VerifiedExternalGlueLegacy F R`,
- an explicit compatibility witness `hcompat : G.compatible n m Γ σ st`.

Important role:
- localize the remaining legacy external glue assumption to one bridge file,
- feed old external inputs into the new explicit V3 entry object,
- let old wrappers reuse the V3 assembly flow without changing the core route.
-/

/-- Package old legacy assumptions into the explicit V3 pieces object. -/
noncomputable def externalPiecesV3_of_legacy_external_assumptions
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st := by
  let hb : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary
      G huse hdyn hgen hstruct hprof hcompat
  let hc : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact
    { structural := hb.structural
      profile := hb.profile
      dynamic := hb.dynamic
      core := hc
      adequacy := hb.adequacy }

/-- The V3 `core` projection is definitionally the remaining legacy core bridge. -/
theorem externalPiecesV3_of_legacy_external_assumptions_core
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (externalPiecesV3_of_legacy_external_assumptions
      G huse hdyn hgen hstruct hprof hcompat).core
      = reflection_fragment_generates_core hgen := by
  rfl

theorem externalPiecesV3_of_legacy_external_assumptions_boundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (externalPiecesV3_of_legacy_external_assumptions
      G huse hdyn hgen hstruct hprof hcompat).toBodyBoundary
      =
    fragments_establish_body_closure_boundary
      G huse hdyn hgen hstruct hprof hcompat := by
  let hb : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary
      G huse hdyn hgen hstruct hprof hcompat
  change mkBodyClosureBoundaryCI hb.structural hb.profile hb.dynamic hb.adequacy = hb
  cases hb
  rfl


/-- Legacy name for the assembled body boundary route into V3. -/
noncomputable def legacyAssembleBodyBoundaryV3
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPiecesV3_of_legacy_external_assumptions
    G huse hdyn hgen hstruct hprof hcompat).toBodyBoundary

/-- The renamed legacy assembled route agrees with the direct legacy theorem. -/
theorem legacyAssembleBodyBoundaryV3_eq_old
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    legacyAssembleBodyBoundaryV3
      G huse hdyn hgen hstruct hprof hcompat
      =
    fragments_establish_body_closure_boundary
      G huse hdyn hgen hstruct hprof hcompat :=
  externalPiecesV3_of_legacy_external_assumptions_boundary
    G huse hdyn hgen hstruct hprof hcompat

end Cpp
