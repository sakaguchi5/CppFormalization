import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.Interface

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosure

Mainline external closure surface after the Stage 7 switch.

方針:
- canonical theorem surface は assembled boundary mainline (`Interface` + `InternalClosureRoadmap`) に接続する。
- old coarse `BodyReady` ベース theorem は `Closure.Legacy.ReflectiveStdClosureLegacy` へ退避済み。
-/

abbrev reflective_std_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  exact InternalClosureRoadmap.function_body_progress_or_diverges
    (reflection_fragment_generates_core hgen)
    (fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof)

abbrev reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  exact InternalClosureRoadmap.stmt_terminates_or_diverges
    (reflection_fragment_generates_core hgen)
    (fragments_establish_body_closure_boundary huse hdyn hgen hstruct hprof)

end Cpp
