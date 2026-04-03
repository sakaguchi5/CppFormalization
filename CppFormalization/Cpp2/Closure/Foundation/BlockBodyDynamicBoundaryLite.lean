import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

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
