import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCoherenceV2

namespace Cpp

/-!
# Closure.External.ReadyFromGlueV3

Any low-level glue implementation still induces a ready-style implementation.
In the redesigned V3, the induced route preserves the canonical runtime and
reflection packages definitionally, and the final boundary agrees by the usual
`BodyClosureBoundaryCI` roundtrip.
-/

noncomputable def readyAssembly_of_glue_v3
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R) :
    VerifiedExternalReadyAssemblyV3 F R where
  compatible := G.compatible
  mkReady := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    let p : ExternalPiecesV3 Γ σ st :=
      assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
    exact p.toBodyBoundary.toBodyReadyCI
  dynamic_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    unfold assembleExternalPiecesV3
    rfl
  structural_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    unfold assembleExternalPiecesV3
    rfl
  profile_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    unfold assembleExternalPiecesV3
    rfl


theorem externalPieces_of_ready_from_glue_v3_boundary_eq
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hsuppRun : F.supportsRuntime n Γ σ st)
    (hgen : R.generates m st)
    (hsuppRefl : R.supportsReflection m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    (externalPieces_of_ready_v3 (readyAssembly_of_glue_v3 G)
      huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary =
      (assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary := by
  let p : ExternalPiecesV3 Γ σ st :=
    assembleExternalPiecesV3 G huse hsuppRun hgen hsuppRefl hcompat
  change p.toBodyBoundary.toBodyReadyCI.toClosureBoundary = p.toBodyBoundary
  exact bodyClosureBoundaryCI_roundtrip p.toBodyBoundary


theorem reflective_std_function_body_closure_v3_via_ready
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_function_body_closure_from_ready_v3
    (readyAssembly_of_glue_v3 G) huse hsuppRun hgen hsuppRefl hcompat


theorem reflective_std_closure_theorem_v3_via_ready
    {F : VerifiedStdFragmentV3} {R : VerifiedReflectionFragmentV3}
    (G : VerifiedExternalGlueV3 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.supportsRuntime n Γ σ st →
    R.generates m st →
    R.supportsReflection m Γ st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_closure_theorem_from_ready_v3
    (readyAssembly_of_glue_v3 G) huse hsuppRun hgen hsuppRefl hcompat

end Cpp
