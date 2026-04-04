import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3

namespace Cpp

/-!
# Closure.External.GlueV3

V3 external glue layer.

This keeps the V2 insight that adequacy must be an explicit responsibility,
while restoring target-indexed applicability assumptions for concrete artifacts.
-/

structure VerifiedExternalGlueV3
    (F : VerifiedStdFragmentV3) (R : VerifiedReflectionFragmentV3) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkAdequacy :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      F.uses n →
      F.supportsDynamic n Γ σ st →
      R.generates m st →
      R.supportsStructural m Γ st →
      R.supportsProfile m Γ st →
      compatible n m Γ σ st →
      BodyDynamicBoundary Γ σ st →
      BodyStructuralBoundary Γ st →
      (hp : BodyControlProfile Γ st) →
      CoreBigStepFragment st →
      BodyAdequacyCI Γ σ st hp

end Cpp
