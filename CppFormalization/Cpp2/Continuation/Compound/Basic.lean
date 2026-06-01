import CppFormalization.Cpp2.Operational.Divergence
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Profile.StaticBoundary.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Adequacy.Body.BodyAdequacyCI

namespace Cpp
namespace CompoundContinuation

/-!
# CompoundContinuation basic surfaces

This directory rebuilds seq, block-cons, and while around one mathematical
pattern:

1. select a concrete operational route;
2. expose post-state preservation separately from replay;
3. materialize a continuation boundary at the selected post-state;
4. attach static/profile adequacy where appropriate;
5. close the continuation by a proof demand;
6. lift the continuation result back to the original compound.

The three instances differ only in the selected route, continuation target, and
semantic lifting constructor:

* `seq`: statement tail;
* `cons`: block tail;
* `while`: same while statement after a normal/continue body step.
-/

/-- A scoped/typed concrete state at a fixed environment. -/
structure PostStateAt (Γ : TypeEnv) (σ : State) : Prop where
  state : ScopedTypedStateConcrete Γ σ

/-- Statement static/profile surface. -/
structure StmtStaticAt (Γ : TypeEnv) (st : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ st

/-- Block-tail static/profile surface in the current/open block environment. -/
structure BlockStaticAt (Γ : TypeEnv) (ss : StmtBlock) : Type where
  static : BlockBodyStaticBoundaryCI Γ ss

/-- Statement adequacy surface at a concrete state. -/
structure StmtAdequacyAt
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : StmtStaticAt Γ st) : Type where
  adequacy : BodyAdequacyCI Γ σ st S.static.profile

/-- Block-tail adequacy surface at a concrete state. -/
structure BlockAdequacyAt
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (S : BlockStaticAt Γ ss) : Type where
  adequacy : BlockBodyAdequacyCI Γ σ ss S.static.profile

end CompoundContinuation
end Cpp
