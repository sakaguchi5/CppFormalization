import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.InterfaceV2

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosureV2

V2 final wrapper: external artifacts explicitly assemble the official mainline
entry object, then the internal roadmap theorem is applied unchanged.
-/



theorem reflective_std_function_body_closure_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  let pieces : ExternalPieces Γ σ st :=
    assembleExternalPieces G huse hgen hcompat
  sorry
  /-
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      pieces.core
      pieces.toBodyBoundary
-/

theorem reflective_std_closure_theorem_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  let p := assembleExternalPieces G huse hgen hcompat
  sorry/-
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core
      p.toBodyBoundary
-/
end Cpp
