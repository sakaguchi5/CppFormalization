import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Dynamic

Path-sensitive post-state dynamic boundaries.

Design point:
- `StmtReadyConcrete` / `BlockReadyConcrete` remain local readiness facts.
- A continuation boundary says that, after a selected route has actually run,
  the continuation can start in the resulting post-state.
- This module contains only the dynamic state/readiness part.  Static/profile
  and adequacy alignment should be layered above it.

This is deliberately not a transport theorem.  Legacy transport providers may
construct these boundaries for now, but the public subject is the continuation
boundary itself.
-/

/-- Post-state dynamic boundary for a statement continuation. -/
structure StmtContinuationDynamicBoundary
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st

/-- Post-state dynamic boundary for a block tail in the current environment.

Unlike `BlockBodyDynamicBoundary`, this does not insert `pushTypeScope`.
It is for a tail of an already-open/current block route such as `s :: ss`.
-/
structure BlockContinuationDynamicBoundary
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  state : ScopedTypedStateConcrete Γ σ
  safe : BlockReadyConcrete Γ σ ss

/-- Statement continuation dynamics can be viewed as the existing body dynamic
boundary. -/
def StmtContinuationDynamicBoundary.toBodyDynamicBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtContinuationDynamicBoundary Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  { state := h.state
    safe := h.safe }

/-- Build a statement continuation dynamic boundary from the existing dynamic
boundary. -/
def StmtContinuationDynamicBoundary.ofBodyDynamicBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyDynamicBoundary Γ σ st) :
    StmtContinuationDynamicBoundary Γ σ st :=
  { state := h.state
    safe := h.safe }

end Cpp
