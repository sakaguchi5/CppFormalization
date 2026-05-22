import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.TailDemand
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ExitLifting

namespace Cpp
namespace WhileClosure2

/-!
# C++-facing surface for while contracts

This file is an explanation surface.  It does not add a broad provider.  It gives
names to the small obligations that a C++ programmer should recognize.
-/

inductive WhileContractKind2 where
  | postStatePreservation
  | conditionReplayAfterNormal
  | conditionReplayAfterContinue
  | bodyReplayAfterNormal
  | bodyReplayAfterContinue
  | loadReadability
  | pointerDerefStability
  | tailAdequacy
  | tailRecursionDemand
deriving DecidableEq, Repr

/-- Explanation surface for a normal backedge. -/
structure NormalBackedgeSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  replay : NormalBackedgeReplay2 route
  note :
    List WhileContractKind2 :=
      [ .postStatePreservation
      , .conditionReplayAfterNormal
      , .bodyReplayAfterNormal ]

def NormalBackedgeSurface2.toReplay
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeSurface2 route) :
    NormalBackedgeReplay2 route :=
  h.replay

/-- Explanation surface for a continue backedge. -/
structure ContinueBackedgeSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  replay : ContinueBackedgeReplay2 route
  note :
    List WhileContractKind2 :=
      [ .postStatePreservation
      , .conditionReplayAfterContinue
      , .bodyReplayAfterContinue ]

def ContinueBackedgeSurface2.toReplay
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeSurface2 route) :
    ContinueBackedgeReplay2 route :=
  h.replay

/--
Full surface for a normal-tail route.  This is the C++-readable decomposition of
the old "while tail provider" idea.
-/
structure NormalTailSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  backedge : NormalBackedgeSurface2 route
  tailAdequacy : NormalTailAdequacyDemand2 route
  tailDemand : NormalTailDemand2 route

/--
Full surface for a continue-tail route.  This is the C++-readable decomposition
of the old "while tail provider" idea.
-/
structure ContinueTailSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  backedge : ContinueBackedgeSurface2 route
  tailAdequacy : ContinueTailAdequacyDemand2 route
  tailDemand : ContinueTailDemand2 route

end WhileClosure2
end Cpp
