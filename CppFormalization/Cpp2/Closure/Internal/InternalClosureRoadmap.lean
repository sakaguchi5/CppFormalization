import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapCI

namespace Cpp

/-!
# Closure.Internal.InternalClosureRoadmap

Mainline internal roadmap after the Stage 7 switch.

方針:
- canonical input boundary は assembled boundary `ClosureV2.BodyClosureBoundaryCI`.
- implementation は `InternalClosureRoadmapCI` の V2 surface を thin wrapper として再利用する。
- old coarse `BodyReady` ベース roadmap は `Closure.Legacy.InternalClosureRoadmapLegacy` へ退避済み。
-/

namespace InternalClosureRoadmap

abbrev BodyBoundary := ClosureV2.BodyClosureBoundaryCI

abbrev function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st :=
  InternalClosureRoadmapCI.body_ready_ci_function_body_progress_or_diverges_v2

abbrev stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyBoundary Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st :=
  InternalClosureRoadmapCI.body_ready_ci_stmt_terminates_or_diverges_v2

end InternalClosureRoadmap

end Cpp
