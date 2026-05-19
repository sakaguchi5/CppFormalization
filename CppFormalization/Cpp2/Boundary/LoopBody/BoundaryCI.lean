import CppFormalization.Cpp2.Boundary.LoopBody.StructuralBoundaryCI
import CppFormalization.Cpp2.Boundary.LoopBody.ProfileCI
import CppFormalization.Cpp2.Boundary.LoopBody.DynamicBoundaryCI
import CppFormalization.Cpp2.Boundary.LoopBody.AdequacyCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.LoopBody.BoundaryCI

Assembled four-layer boundary for a single `while` body.

The loop body has local `break` and `continue` exits, so it is intentionally not
represented as an ordinary top-level `BodyClosureBoundaryCI`.
-/

/-- assembled 4-layer boundary for a single `while` body. -/
structure LoopBodyBoundaryCI (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  structural : LoopBodyStructuralBoundary Γ body
  profile : LoopBodyControlProfile Γ body
  dynamic : LoopBodyDynamicBoundary Γ σ body
  adequacy : LoopBodyAdequacyCI Γ σ body profile

/-- constructor-style helper mirroring `mkBodyClosureBoundaryCI`. -/
def mkLoopBodyBoundaryCI
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hs : LoopBodyStructuralBoundary Γ body)
    (hp : LoopBodyControlProfile Γ body)
    (hd : LoopBodyDynamicBoundary Γ σ body)
    (ha : LoopBodyAdequacyCI Γ σ body hp) :
    LoopBodyBoundaryCI Γ σ body :=
  { structural := hs
    profile := hp
    dynamic := hd
    adequacy := ha }

end Cpp
