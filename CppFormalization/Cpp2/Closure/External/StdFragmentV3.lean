import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.StdFragmentV3

V3 external interface for the std/runtime-side fragment.

Compared with V2, this restores an explicit target-indexed applicability
relation. This avoids the overly-strong reading that one artifact `n`
automatically yields a dynamic boundary for arbitrary `Γ σ st`.
-/

structure VerifiedStdFragmentV3 where
  Name : Type
  uses : Name → Prop
  supportsDynamic : Name → TypeEnv → State → CppStmt → Prop

  mkDynamic :
    ∀ {n : Name} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n →
      supportsDynamic n Γ σ st →
      BodyDynamicBoundary Γ σ st

end Cpp
