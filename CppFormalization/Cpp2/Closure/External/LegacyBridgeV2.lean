import CppFormalization.Cpp2.Closure.External.Interface
import CppFormalization.Cpp2.Closure.External.AssembleV2

namespace Cpp

/-!
# Closure.External.LegacyBridgeV2

Bridge the old external assumption-style interface into the explicit V2
assembly object `ExternalPieces`.

Important role:
- localize the old monolithic external axioms to one bridge file,
- feed old external inputs into the new explicit V2 entry object,
- let old wrappers reuse the V2 assembly flow without changing their surface.
-/

noncomputable def externalPieces_of_legacy_external_assumptions
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    ExternalPieces Γ σ st := by
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


noncomputable def legacyAssembleBodyBoundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPieces_of_legacy_external_assumptions huse hdyn hgen hstruct hprof).toBodyBoundary

end Cpp
