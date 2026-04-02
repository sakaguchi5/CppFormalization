import CppFormalization.Cpp2.Closure.Legacy.InternalClosureRoadmapLegacy
import CppFormalization.Cpp2.Closure.Legacy.InterfaceLegacy

namespace Cpp.Legacy

/-!
# Closure.Legacy.ReflectiveStdClosureLegacy

第7段階で mainline から退避した old coarse external theorem surface.
-/

theorem reflective_std_function_body_closure
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    R.generates m st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hboundary hgen
  have hready : BodyReady Γ σ st :=
    std_fragment_establishes_body_ready huse hboundary
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact body_ready_function_body_progress_or_diverges hfrag hready

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.establishesBoundary n Γ σ st →
    R.generates m st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hboundary hgen
  have hready : BodyReady Γ σ st :=
    std_fragment_establishes_body_ready huse hboundary
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_generates_core hgen
  exact body_ready_stmt_terminates_or_diverges hfrag hready

end Cpp.Legacy
