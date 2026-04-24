import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.LegacyBridgeV3

namespace Cpp

theorem reflective_std_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesStatic m Γ st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hstatic hcompat
  have hcl : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary
      (G := G)
      (huse := huse)
      (hdyn := hdyn)
      (hgen := hgen)
      (hstruct := hstruct)
      (hstatic := hstatic)
      (hcompat := hcompat)
  sorry
  --exact function_body_closure_of_bodyClosureBoundaryCI hcl

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesStatic m Γ st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof hcompat
  sorry
  /-
  let p : ExternalPiecesV3 Γ σ st :=
    externalPiecesV3_of_legacy_external_assumptions
      G huse hdyn hgen hstruct hprof hcompat
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core p.toBodyBoundary
-/
end Cpp
