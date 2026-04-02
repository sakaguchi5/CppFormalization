import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapCI
import CppFormalization.Cpp2.Closure.External.InterfaceCI

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosureCI

第6段階の V2 external closure surface.

- external adapter (`InterfaceCI`) から assembled boundary を得る。
- internal CI roadmap の V2 surface へ接続する。
- old `ReflectiveStdClosure` は legacy surface として残す。
-/

theorem reflective_std_function_body_closure_v2
    {F : VerifiedStdFragmentCI} {R : VerifiedReflectionFragmentCI}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  have hboundary : ClosureV2.BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary_v2 huse hdyn hgen hstruct hprof
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core_v2 hgen
  exact InternalClosureRoadmapCI.body_ready_ci_function_body_progress_or_diverges_v2 hfrag hboundary

theorem reflective_std_closure_theorem_v2
    {F : VerifiedStdFragmentCI} {R : VerifiedReflectionFragmentCI}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesDynamic n Γ σ st →
    R.generates m st →
    R.establishesStructural m Γ st →
    R.establishesProfile m Γ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hdyn hgen hstruct hprof
  have hboundary : ClosureV2.BodyClosureBoundaryCI Γ σ st :=
    fragments_establish_body_closure_boundary_v2 huse hdyn hgen hstruct hprof
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core_v2 hgen
  exact InternalClosureRoadmapCI.body_ready_ci_stmt_terminates_or_diverges_v2 hfrag hboundary

end Cpp
