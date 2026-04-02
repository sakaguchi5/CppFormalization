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
  exact InternalClosureRoadmapCI.body_closure_function_body_progress_or_diverges hfrag hboundary

theorem stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  exact InternalClosureRoadmapCI.body_closure_stmt_terminates_or_diverges hfrag hboundary

end InternalClosureRoadmap

end Cpp
