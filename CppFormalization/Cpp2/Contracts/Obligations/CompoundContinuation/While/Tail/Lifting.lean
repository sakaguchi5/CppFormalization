import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.While.Tail.ProofDemand

namespace Cpp
namespace CompoundContinuation
namespace While
namespace Tail

/-!
# While tail lifting
-/

namespace Normal

theorem step
    {Γ : TypeEnv} {σ σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    {ctrl : CtrlResult}
    (tailStep : BigStepStmt σ1 (.whileStmt c body) ctrl σ2) :
    BigStepStmt σ (.whileStmt c body) ctrl σ2 := by
  exact BigStepStmt.whileTrueNormal cond.hcondTrue route.hbody tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (tailDiv : BigStepStmtDiv σ1 (.whileStmt c body)) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    BigStepStmtDiv.whileIter
      cond.hcondTrue
      (Or.inl route.hbody)
      tailDiv

theorem closeAndLiftFromContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (continuation : Backedge.NormalContinuationInput route)
    (tailProof : NormalProofDemand route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  let dyn : StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
    continuation.toDynamicBoundary
  match tailProof.demand.close dyn with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ1 := σ1) (σ2 := σ2)
              (c := c) (body := body)
              (entry := entry) (cond := cond) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ1 := σ1)
            (c := c) (body := body)
            (entry := entry) (cond := cond) (route := route)
            hdiv)

theorem closeAndLift
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (pkg : NormalPackage route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    closeAndLiftFromContinuationAndProof
      (Γ := Γ) (σ := σ) (σ1 := σ1)
      (c := c) (body := body)
      (entry := entry) (cond := cond) (route := route)
      pkg.continuation
      pkg.tailProof

end Normal

namespace Continued

theorem step
    {Γ : TypeEnv} {σ σ1 σ2 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    {ctrl : CtrlResult}
    (tailStep : BigStepStmt σ1 (.whileStmt c body) ctrl σ2) :
    BigStepStmt σ (.whileStmt c body) ctrl σ2 := by
  exact BigStepStmt.whileTrueContinue cond.hcondTrue route.hbody tailStep

theorem diverges
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (tailDiv : BigStepStmtDiv σ1 (.whileStmt c body)) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    BigStepStmtDiv.whileIter
      cond.hcondTrue
      (Or.inr route.hbody)
      tailDiv

theorem closeAndLiftFromContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (continuation : Backedge.ContinueContinuationInput route)
    (tailProof : ContinueProofDemand route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  let dyn : StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
    continuation.toDynamicBoundary
  match tailProof.demand.close dyn with
  | Or.inl ⟨ctrl, σ2, hstep⟩ =>
      exact
        Or.inl
          ⟨ctrl, σ2,
            step
              (Γ := Γ) (σ := σ) (σ1 := σ1) (σ2 := σ2)
              (c := c) (body := body)
              (entry := entry) (cond := cond) (route := route)
              (ctrl := ctrl)
              hstep⟩
  | Or.inr hdiv =>
      exact
        Or.inr
          (diverges
            (Γ := Γ) (σ := σ) (σ1 := σ1)
            (c := c) (body := body)
            (entry := entry) (cond := cond) (route := route)
            hdiv)

theorem closeAndLift
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (pkg : ContinuePackage route) :
    (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    closeAndLiftFromContinuationAndProof
      (Γ := Γ) (σ := σ) (σ1 := σ1)
      (c := c) (body := body)
      (entry := entry) (cond := cond) (route := route)
      pkg.continuation
      pkg.tailProof

end Continued

end Tail
end While
end CompoundContinuation
end Cpp
