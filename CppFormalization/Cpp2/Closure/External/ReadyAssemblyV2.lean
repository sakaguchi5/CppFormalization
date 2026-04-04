import CppFormalization.Cpp2.Closure.External.AssembleV2
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap

namespace Cpp

/-!
# Closure.External.ReadyAssemblyV2

A stronger external assembly route:
if an external system can directly produce an integrated `BodyReadyCI`,
then the V2 explicit pieces are obtained canonically by projection.

Design intent:
- `GlueV2` exposes the hidden semantic glue.
- `ReadyAssemblyV2` provides a more practical route for implementations
  that can already construct a single integrated witness `BodyReadyCI`.
- Both routes still land in the same official object `ExternalPieces`.
-/

structure VerifiedExternalReadyAssemblyV2
    (F : VerifiedStdFragmentV2) (R : VerifiedReflectionFragmentV2) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkReady :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      F.uses n →
      R.generates m st →
      compatible n m Γ σ st →
      BodyReadyCI Γ σ st

def externalPieces_of_ready_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (A : VerifiedExternalReadyAssemblyV2 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hgen : R.generates m st)
    (hcompat : A.compatible n m Γ σ st) :
    ExternalPieces Γ σ st := by
  let hr : BodyReadyCI Γ σ st := A.mkReady huse hgen hcompat
  let hc : CoreBigStepFragment st := R.mkCore hgen
  exact
    { structural := hr.toStructural
      profile := hr.toProfile
      dynamic := hr.toDynamic
      core := hc
      adequacy := hr.toAdequacy }

def assembleBodyBoundary_of_ready_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (A : VerifiedExternalReadyAssemblyV2 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hgen : R.generates m st)
    (hcompat : A.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  (externalPieces_of_ready_v2 A huse hgen hcompat).toBodyBoundary

theorem reflective_std_function_body_closure_from_ready_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (A : VerifiedExternalReadyAssemblyV2 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    A.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  let p := externalPieces_of_ready_v2 A huse hgen hcompat
  exact
    InternalClosureRoadmap.function_body_progress_or_diverges
      p.core
      p.toBodyBoundary

theorem reflective_std_closure_theorem_from_ready_v2
    {F : VerifiedStdFragmentV2} {R : VerifiedReflectionFragmentV2}
    (A : VerifiedExternalReadyAssemblyV2 F R)
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    R.generates m st →
    A.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hgen hcompat
  let p := externalPieces_of_ready_v2 A huse hgen hcompat
  exact
    InternalClosureRoadmap.stmt_terminates_or_diverges
      p.core
      p.toBodyBoundary

end Cpp
