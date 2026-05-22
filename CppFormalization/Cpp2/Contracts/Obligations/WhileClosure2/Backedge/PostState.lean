import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Route.Body

namespace Cpp
namespace WhileClosure2

/-!
# Backedge post-state preservation

This layer is intentionally separated from replay.  Post-state preservation is
expected to come from preservation theorems, whereas replay invariants are the
genuinely program-dependent C++ obligations.
-/

structure NormalBackedgePostState2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Prop where
  postState : PostStateAt Γ σ'

structure ContinueBackedgePostState2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Prop where
  postState : PostStateAt Γ σ'

end WhileClosure2
end Cpp
