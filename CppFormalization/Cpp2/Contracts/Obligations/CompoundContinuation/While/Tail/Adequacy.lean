import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.While.Backedge.Continuation

namespace Cpp
namespace CompoundContinuation
namespace While
namespace Tail

/-!
# While tail adequacy
-/

structure WhileTailAdequacy
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ (.whileStmt c body)
  adequacy : BodyAdequacyCI Γ σ (.whileStmt c body) static.profile

structure NormalAdequacyDemand
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Type where
  tailAdequacy : WhileTailAdequacy Γ σ1 c body

structure ContinueAdequacyDemand
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Type where
  tailAdequacy : WhileTailAdequacy Γ σ1 c body

end Tail
end While
end CompoundContinuation
end Cpp
