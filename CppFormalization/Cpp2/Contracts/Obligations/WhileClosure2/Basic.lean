import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Boundary.Static.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Boundary.Adequacy.BodyAdequacyCI

namespace Cpp
namespace WhileClosure2

/-!
# WhileClosure2 basic surfaces

This directory is a zero-base clean-room reconstruction of the while-closure
shape.

The intended mathematical split is:

* entry/local readiness;
* condition-first routes;
* body-local progress under the true route;
* post-state preservation;
* replay invariants;
* derived continuation boundaries;
* tail adequacy;
* proof recursion demand;
* theorem-backed semantic lifting.

In particular, the program-facing contract is not the whole while closure.
The genuinely C++-dependent part is the replay/invariant obligation needed to
start the next iteration after the body exits by `normal` or `continue`.
-/

/-- A scoped/typed post-state at a fixed concrete environment. -/
structure PostStateAt (Γ : TypeEnv) (σ : State) : Prop where
  state : ScopedTypedStateConcrete Γ σ

/-- Static/profile surface for a while statement. -/
structure WhileStaticAt (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ (.whileStmt c body)

/-- Semantic adequacy surface for a while statement at a concrete state. -/
structure WhileAdequacyAt
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt)
    (S : WhileStaticAt Γ c body) : Type where
  adequacy : BodyAdequacyCI Γ σ (.whileStmt c body) S.static.profile

end WhileClosure2
end Cpp
