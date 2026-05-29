import CppFormalization.Cpp2.Entry.StaticSafety.BodyDynamicBoundary

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.LoopBody.DynamicBoundaryCI

Runtime entry boundary for a single `while` body.
-/

/-- state-dependent entry boundary for a loop body. -/
structure LoopBodyDynamicBoundary (Γ : TypeEnv) (σ : State) (body : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ body

end Cpp
