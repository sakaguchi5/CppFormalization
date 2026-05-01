import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapCI

namespace Cpp

namespace InternalClosureRoadmap

abbrev BodyBoundary := BodyClosureBoundaryCI

theorem function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  exact Cpp.body_closure_ci_function_body_progress_or_diverges hfrag hboundary

theorem stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  rcases Cpp.body_closure_ci_function_body_progress_or_diverges hfrag hboundary with hbody | hdiv
  · left
    rcases hbody with ⟨ex, σ', hfb⟩
    cases ex with
    | fellThrough =>
        refine ⟨.normal, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
    | returned rv =>
        refine ⟨.returnResult rv, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
  · exact Or.inr hdiv

end InternalClosureRoadmap

end Cpp
