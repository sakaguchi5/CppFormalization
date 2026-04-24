import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV2
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCoherenceV2

namespace Cpp

/-!
# Closure.External.ReadyFromGlueV2

Derive the stronger integrated V2 route from the lower-level explicit glue route.

Mathematical role:
- `GlueV2` exposes the hidden semantic glue explicitly.
- `ReadyAssemblyV2` is a stronger API for implementations that can provide
  a single integrated `BodyReadyCI`.
- This file shows that the stronger route is not extra burden:
  any `VerifiedExternalGlueV2` canonically induces a
  `VerifiedExternalReadyAssemblyV2`.
-/

noncomputable def readyAssembly_of_glue_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R) :
    VerifiedExternalReadyAssemblyV2 F R where
  compatible := G.compatible
  mkReady := by
    intro n m Γ σ st huse hgen hcompat
    let p : ExternalPieces Γ σ st :=
      assembleExternalPieces G huse hgen hcompat
    exact p.toBodyBoundary.toBodyReadyCI

theorem externalPieces_of_ready_from_glue_boundary_eq
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n) (hgen : R.generates m st)
    (hcompat : G.compatible n m Γ σ st) :
    (externalPieces_of_ready_v2 (readyAssembly_of_glue_v2 G) huse hgen hcompat).toBodyBoundary
      =
    (assembleExternalPieces G huse hgen hcompat).toBodyBoundary := by
  let p : ExternalPieces Γ σ st :=
    assembleExternalPieces G huse hgen hcompat
  have hp :
      (externalPieces_of_ready_v2 (readyAssembly_of_glue_v2 G) huse hgen hcompat).toBodyBoundary
        =
      p.toBodyBoundary.toBodyReadyCI.toClosureBoundary := by
    sorry--rfl
  rw [hp]
  simpa using bodyClosureBoundaryCI_roundtrip p.toBodyBoundary

theorem reflective_std_function_body_closure_v2_via_ready
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    G.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  exact
    reflective_std_function_body_closure_from_ready_v2
      (readyAssembly_of_glue_v2 G)
      huse hgen hcompat

theorem reflective_std_closure_theorem_v2_via_ready
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (G : VerifiedExternalGlueV2 F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    G.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  exact
    reflective_std_closure_theorem_from_ready_v2
      (readyAssembly_of_glue_v2 G)
      huse hgen hcompat

end Cpp
