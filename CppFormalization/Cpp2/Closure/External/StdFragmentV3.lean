import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.External.StdFragmentV3

Stage 2A redesign:
- the std/runtime side no longer directly returns a bare dynamic boundary,
- instead it returns a target-indexed runtime package,
- this makes the external layer package-first rather than piece-first.
-/

structure RuntimePiecesV3 (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  dynamic : BodyDynamicBoundary Γ σ st

structure VerifiedStdFragmentV3 where
  Name : Type
  uses : Name → Prop
  supportsRuntime : Name → TypeEnv → State → CppStmt → Prop
  mkRuntime :
    ∀ {n : Name} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n →
      supportsRuntime n Γ σ st →
      RuntimePiecesV3 Γ σ st

end Cpp
