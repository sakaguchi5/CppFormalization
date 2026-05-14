import CppFormalization.Cpp2.Static.Safety.Readiness
import CppFormalization.Cpp2.Static.Safety.StateInvariantConcrete

/-!
# CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary

State-dependent dynamic entry boundaries for top-level function bodies.

This module lives in `Static.Safety` because it is only a state-dependent
entry safety boundary:
- a concrete state invariant;
- a concrete readiness assumption.

It intentionally does not depend on Closure or adequacy.
-/
namespace Cpp

/-!
# Closure.Foundation.BodyDynamicBoundary

四層分離の第3層。

ここでは「今の state から安全に開始できるか」という
state-dependent entry boundary だけを切り出す。
structural admission や CI summary はここへ入れない。
-/

/-- State-dependent dynamic entry boundary for a top-level function body. -/
structure BodyDynamicBoundary (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st

/-- State-dependent dynamic entry boundary for an opened block body. -/
structure BlockBodyDynamicBoundary (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  state : ScopedTypedStateConcrete (pushTypeScope Γ) σ
  safe : BlockReadyConcrete (pushTypeScope Γ) σ ss

theorem BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hstate : ScopedTypedStateConcrete Γ σ)
    (hstmt : StmtReadyConcrete Γ σ st) :
    BodyDynamicBoundary Γ σ st := by
  exact ⟨hstate, hstmt⟩

end Cpp
