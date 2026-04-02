import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapCI

namespace Cpp

/-!
# Closure.Internal.InternalClosureRoadmap

第7段階の mainline internal roadmap.

方針:
- mainline は assembled boundary (`ClosureV2.BodyClosureBoundaryCI`) を入口にする。
- old coarse `BodyReady` ベースの roadmap は legacy へ退避する。
- 実装本体は `InternalClosureRoadmapCI` の V2 surface を再利用する。
-/

namespace InternalClosureRoadmap

abbrev BodyBoundary := ClosureV2.BodyClosureBoundaryCI

theorem function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  exact InternalClosureRoadmapCI.body_ready_ci_function_body_progress_or_diverges_v2 hfrag hboundary

theorem stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  exact InternalClosureRoadmapCI.body_ready_ci_stmt_terminates_or_diverges_v2 hfrag hboundary

end InternalClosureRoadmap

end Cpp
