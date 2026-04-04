import CppFormalization.Cpp2.Closure.External.StdFragmentV2
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV2

namespace Cpp

/-!
# Closure.External.GlueV2

V2 external glue layer.

This layer is where the previously-hidden semantic glue is made explicit.
In particular, adequacy is no longer smuggled inside a monolithic external
assembly axiom; it is a first-class responsibility of the glue.
-/

structure VerifiedExternalGlueV2
    (F : VerifiedStdFragmentV2) (R : VerifiedReflectionFragmentV2) where
  compatible :
    F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkAdequacy :
    ∀ {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      compatible n m Γ σ st →
      BodyDynamicBoundary Γ σ st →
      BodyStructuralBoundary Γ st →
      (hp : BodyControlProfile Γ st) →
      CoreBigStepFragment st →
      BodyAdequacyCI Γ σ st hp

end Cpp
