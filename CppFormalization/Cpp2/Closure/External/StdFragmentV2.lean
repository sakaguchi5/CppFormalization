import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.StdFragmentV2

V2 external interface: the std/runtime-side fragment is responsible only for
producing the dynamic entry boundary.
-/

structure VerifiedStdFragmentV2 where
  Name : Type
  uses : Name → Prop
  mkDynamic :
    ∀ {n : Name} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n → BodyDynamicBoundary Γ σ st

end Cpp
