import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCoherenceV2

namespace Cpp

/-!
# Closure.External.ReadyFromGlueV3

Derive the stronger integrated target-indexed V3 route from the lower-level
explicit glue route.

This shows that the high-level `BodyReadyCI` route is not extra burden:
any V3 glue implementation canonically induces a ready-style implementation.
-/

noncomputable def readyAssembly_of_glue_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R) :
    VerifiedExternalReadyAssemblyV3 F R where
  compatible := G.compatible
  mkReady := by
    intro n m Γ σ st huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
    let p : ExternalPiecesV3 Γ σ st :=
      assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
    exact p.toBodyBoundary.toBodyReadyCI

theorem externalPieces_of_ready_from_glue_v3_boundary_eq
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppDyn : F.supportsDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hsuppStruct : R.supportsStructural m Γ st)
    (hsuppProf : R.supportsProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 (readyAssembly_of_glue_v3 G)
        huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toBodyBoundary
      =
    (assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat).toBodyBoundary := by
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppDyn hgen hsuppStruct hsuppProf hcompat
  change p.toBodyBoundary.toBodyReadyCI.toClosureBoundary = p.toBodyBoundary
  exact bodyClosureBoundaryCI_roundtrip p.toBodyBoundary

theorem reflective_std_function_body_closure_v3_via_ready
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
  exact
    reflective_std_function_body_closure_from_ready_v3
      (readyAssembly_of_glue_v3 G)
      huse hsuppDyn hgen hsuppStruct hsuppProf hcompat

theorem reflective_std_closure_theorem_v3_via_ready
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
  exact
    reflective_std_closure_theorem_from_ready_v3
      (readyAssembly_of_glue_v3 G)
      huse hsuppDyn hgen hsuppStruct hsuppProf hcompat

end Cpp
