import CppFormalization.Cpp2.Static.Safety.Readiness
import CppFormalization.Cpp2.Static.Safety.StateInvariantConcrete

/-!
# CppFormalization.Cpp2.Static.Safety.BlockBodyDynamicBoundaryLite

State-dependent dynamic entry boundary for opened lite block bodies.

This module lives in `Static.Safety` because it is only a state-dependent
entry safety boundary:
- a concrete state invariant;
- a concrete readiness assumption.

It intentionally does not depend on Closure or adequacy.
-/
namespace Cpp

/-!
# Closure.Foundation.BlockBodyDynamicBoundaryLite

E-lite block-body 用の dynamic boundary.

方針:
- opened block body の dynamic layer は outer Γ ではなく、
  現在の local type environment `Λ` で直接 index する。
- これにより head normal 後の tail environment `Δ` を honest に表現できる。
-/


/-- State-dependent dynamic entry boundary for an opened lite block body. -/
structure BlockBodyDynamicBoundaryLite
    (Λ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  state : ScopedTypedStateConcrete Λ σ
  safe : BlockReadyConcrete Λ σ ss

end Cpp
