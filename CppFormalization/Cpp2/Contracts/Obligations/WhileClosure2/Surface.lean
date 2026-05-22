import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Progress.BodyLocal
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Exit.Lifting

namespace Cpp
namespace WhileClosure2

/-!
# C++-facing surface

This file gives names to the three different kinds of obligations that used to
be mixed together:

* program contracts;
* theorem obligations;
* proof-architecture demands.
-/

inductive WhileProgramContractKind2 where
  | conditionReplayAfterNormal
  | conditionReplayAfterContinue
  | bodyReplayAfterNormal
  | bodyReplayAfterContinue
  | loadReadability
  | pointerDerefStability
deriving DecidableEq, Repr

inductive WhileTheoremObligationKind2 where
  | postStatePreservation
  | tailAdequacy
  | exitLifting
  | tailLifting
deriving DecidableEq, Repr

inductive WhileProofDemandKind2 where
  | bodyLocalProgress
  | tailRecursionDemand
deriving DecidableEq, Repr

/-- Explanation surface for a normal backedge. -/
structure NormalBackedgeSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  postState : NormalBackedgePostState2 route
  replay : NormalBackedgeReplayInvariant2 route
  programContracts : List WhileProgramContractKind2 :=
    [ .conditionReplayAfterNormal
    , .bodyReplayAfterNormal ]
  theoremObligations : List WhileTheoremObligationKind2 :=
    [ .postStatePreservation ]

def NormalBackedgeSurface2.toContinuationInput
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeSurface2 route) :
    NormalBackedgeContinuationInput2 route :=
  { postState := h.postState
    replay := h.replay }

/-- Explanation surface for a continue backedge. -/
structure ContinueBackedgeSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  postState : ContinueBackedgePostState2 route
  replay : ContinueBackedgeReplayInvariant2 route
  programContracts : List WhileProgramContractKind2 :=
    [ .conditionReplayAfterContinue
    , .bodyReplayAfterContinue ]
  theoremObligations : List WhileTheoremObligationKind2 :=
    [ .postStatePreservation ]

def ContinueBackedgeSurface2.toContinuationInput
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeSurface2 route) :
    ContinueBackedgeContinuationInput2 route :=
  { postState := h.postState
    replay := h.replay }

/-- Full surface for a normal-tail route. -/
structure NormalTailSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  backedge : NormalBackedgeSurface2 route
  tailAdequacy : NormalTailAdequacyDemand2 route
  tailProof : NormalTailProofDemand2 route
  theoremObligations : List WhileTheoremObligationKind2 :=
    [ .tailAdequacy
    , .tailLifting ]
  proofDemands : List WhileProofDemandKind2 :=
    [ .tailRecursionDemand ]

def NormalTailSurface2.toPackage
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalTailSurface2 route) :
    NormalTailPackage2 route :=
  { continuation := h.backedge.toContinuationInput
    adequacy := h.tailAdequacy
    tailProof := h.tailProof }

/-- Full surface for a continue-tail route. -/
structure ContinueTailSurface2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  backedge : ContinueBackedgeSurface2 route
  tailAdequacy : ContinueTailAdequacyDemand2 route
  tailProof : ContinueTailProofDemand2 route
  theoremObligations : List WhileTheoremObligationKind2 :=
    [ .tailAdequacy
    , .tailLifting ]
  proofDemands : List WhileProofDemandKind2 :=
    [ .tailRecursionDemand ]

def ContinueTailSurface2.toPackage
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueTailSurface2 route) :
    ContinueTailPackage2 route :=
  { continuation := h.backedge.toContinuationInput
    adequacy := h.tailAdequacy
    tailProof := h.tailProof }

end WhileClosure2
end Cpp
