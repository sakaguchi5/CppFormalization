import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.Interface

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
  have hboundary : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof
  have hfrag : CoreBigStepFragment st := reflection_fragment_generates_core hgen
  exact InternalClosureRoadmap.function_body_progress_or_diverges hfrag hboundary

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
  have hboundary : BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof
  have hfrag : CoreBigStepFragment st := reflection_fragment_generates_core hgen
  exact InternalClosureRoadmap.stmt_terminates_or_diverges hfrag hboundary

end Cpp
