import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.AssembleV3

namespace Cpp

/-!
# Closure.External.LegacyBridgeV3

Bridge the old external assumption-style interface into the target-indexed V3
assembly object `ExternalPiecesV3`.

Important role:
- localize the old monolithic external axioms to one bridge file,
- feed old external inputs into the new explicit V3 entry object,
- let old wrappers reuse the V3 assembly flow without changing their surface.
-/

noncomputable def externalPiecesV3_of_legacy_external_assumptions
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    ExternalPiecesV3 Γ σ st := by
  let hb : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof
  let hc : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact
    { structural := hb.structural
      profile := hb.profile
      dynamic := hb.dynamic
      core := hc
      adequacy := hb.adequacy }

theorem externalPiecesV3_of_legacy_external_assumptions_core
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    (externalPiecesV3_of_legacy_external_assumptions
        huse hdyn hgen hstruct hprof).core
      =
    reflection_fragment_generates_core hgen := by
  rfl

theorem externalPiecesV3_of_legacy_external_assumptions_boundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    (externalPiecesV3_of_legacy_external_assumptions
        huse hdyn hgen hstruct hprof).toBodyBoundary
      =
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof := by
  let hb : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof
  change mkBodyClosureBoundaryCI hb.structural hb.profile hb.dynamic hb.adequacy = hb
  cases hb
  rfl

noncomputable def legacyAssembleBodyBoundaryV3
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPiecesV3_of_legacy_external_assumptions
      huse hdyn hgen hstruct hprof).toBodyBoundary

theorem legacyAssembleBodyBoundaryV3_eq_old
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    legacyAssembleBodyBoundaryV3 huse hdyn hgen hstruct hprof
      =
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof :=
  externalPiecesV3_of_legacy_external_assumptions_boundary
    huse hdyn hgen hstruct hprof

end Cpp
