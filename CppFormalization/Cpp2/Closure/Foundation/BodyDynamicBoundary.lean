import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp.ClosureV2

/-!
# Closure.Foundation.BodyDynamicBoundary

四層分離の第3層: state-dependent な entry boundary.

役割:
- 現在の状態から statement / opened block body を安全に開始できることを表す。
- concrete readiness / concrete invariant を正準語彙として採用する。
-/

structure BodyDynamicBoundary (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st

structure BlockBodyDynamicBoundary (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  state : ScopedTypedStateConcrete (pushTypeScope Γ) σ
  safe : BlockReadyConcrete (pushTypeScope Γ) σ ss

end Cpp.ClosureV2
