import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Boundary.Static.BodyStaticBoundaryCI
import CppFormalization.Cpp2.Boundary.Adequacy.BodyAdequacyCI

namespace Cpp
namespace WhileClosure2

/-!
# WhileClosure2: clean-room while scaffold

This directory is a clean-room reconstruction of the while closure/reentry
story.  It intentionally does not import the existing while provider/kernel
modules from `Closure.Internal`.

Design principles:

* `while` is not one opaque axiom/provider.
* Entry, condition routing, body routing, exit lifting, backedge replay,
  tail adequacy, and recursion demand are separate objects.
* Readiness is local.
* Backedge continuation is path-sensitive.
* The genuinely program-dependent contract is backedge replay/invariance.
-/

/-- Post-state preservation for a concrete environment/state pair. -/
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
