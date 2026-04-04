import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.LegacyBridgeV3

namespace Cpp

theorem reflective_std_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  let p : ExternalPiecesV3 Γ σ st :=
    externalPiecesV3_of_legacy_external_assumptions
      huse hdyn hgen hstruct hprof
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      p.core
      p.toBodyBoundary

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  let p : ExternalPiecesV3 Γ σ st :=
    externalPiecesV3_of_legacy_external_assumptions
      huse hdyn hgen hstruct hprof
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core
      p.toBodyBoundary

end Cpp
