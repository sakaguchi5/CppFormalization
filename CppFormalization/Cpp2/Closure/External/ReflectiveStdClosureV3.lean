import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.InterfaceV3

namespace Cpp

/-!
# Closure.External.ReflectiveStdClosureV3

V3 final wrapper: target-indexed external artifacts explicitly assemble the
official mainline entry object, then the internal roadmap theorem is applied
unchanged.
-/

theorem reflective_std_function_body_closure_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsDynamic n Γ σ st →
    R.generates m st →
    R.supportsStructural m Γ st →
    R.supportsProfile m Γ st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      p.core
      p.toBodyBoundary

theorem reflective_std_closure_theorem_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsDynamic n Γ σ st →
    R.generates m st →
    R.supportsStructural m Γ st →
    R.supportsProfile m Γ st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core
      p.toBodyBoundary

end Cpp
