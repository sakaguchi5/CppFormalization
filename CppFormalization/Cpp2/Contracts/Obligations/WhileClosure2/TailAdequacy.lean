import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BackedgeContinuation

namespace Cpp
namespace WhileClosure2

/-!
# Tail adequacy

Tail adequacy is intentionally separate from backedge replay.  Replay says that
the next iteration can start.  Adequacy says that the selected static/profile
package explains the semantic outcomes at the post-state.
-/

structure WhileTailAdequacy2
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ (.whileStmt c body)
  adequacy : BodyAdequacyCI Γ σ (.whileStmt c body) static.profile

structure NormalTailAdequacyDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  tailAdequacy : WhileTailAdequacy2 Γ σ' c body

structure ContinueTailAdequacyDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  tailAdequacy : WhileTailAdequacy2 Γ σ' c body

end WhileClosure2
end Cpp
