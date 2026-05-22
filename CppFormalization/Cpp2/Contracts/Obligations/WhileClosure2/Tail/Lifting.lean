import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.ProofDemand

namespace Cpp
namespace WhileClosure2

/-!
# Tail lifting

Body-normal and body-continue routes do not immediately exit the while.  They
enter the same while at a post-state, and the tail result must be lifted one
iteration back.
-/

namespace NormalTailLifting2

theorem step
    {Γ : TypeEnv} {σ σ' σ2 : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    {ctrl : CtrlResult}
    (tailStep : BigStepStmt σ' (.whileStmt c body) ctrl σ2) :
    BigStepStmt σ (.whileStmt c body) ctrl σ2 := by
  exact BigStepStmt.whileTrueNormal cond.hcondTrue route.hbody tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (tailDiv : BigStepStmtDiv σ' (.whileStmt c body)) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    BigStepStmtDiv.whileIter
      cond.hcondTrue
      (Or.inl route.hbody)
      tailDiv

theorem closeAndLift
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (pkg : NormalTailPackage2 route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  match pkg.closeTail with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ' := σ') (σ2 := σ2)
              (c := c) (body := body)
              (entry := entry) (cond := cond) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ' := σ')
            (c := c) (body := body)
            (entry := entry) (cond := cond) (route := route)
            hdiv)

end NormalTailLifting2

namespace ContinueTailLifting2

theorem step
    {Γ : TypeEnv} {σ σ' σ2 : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    {ctrl : CtrlResult}
    (tailStep : BigStepStmt σ' (.whileStmt c body) ctrl σ2) :
    BigStepStmt σ (.whileStmt c body) ctrl σ2 := by
  exact BigStepStmt.whileTrueContinue cond.hcondTrue route.hbody tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (tailDiv : BigStepStmtDiv σ' (.whileStmt c body)) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    BigStepStmtDiv.whileIter
      cond.hcondTrue
      (Or.inr route.hbody)
      tailDiv

theorem closeAndLift
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (pkg : ContinueTailPackage2 route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  match pkg.closeTail with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ' := σ') (σ2 := σ2)
              (c := c) (body := body)
              (entry := entry) (cond := cond) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ' := σ')
            (c := c) (body := body)
            (entry := entry) (cond := cond) (route := route)
            hdiv)

end ContinueTailLifting2

end WhileClosure2
end Cpp
