import CppFormalization.Cpp3.Soundness.Instantiate.FirstFive
import CppFormalization.Cpp3.Soundness.Semantic.While

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.While

Instantiation of the closed structural while clause.

The proof is intentionally provider-based.  It does not assume a global axiom:
it exposes exactly the cross-layer data needed by a safe C++ while-loop:

* after a true guard, a boundary for the body is available;
* after a body `normal`/`continue` result, a reentry continuation is available.

False guard, break, return, body divergence, and reentry propagation are then
pure semantic consequences.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate

/-- Provides a body boundary after a true while guard. -/
structure WhileBodyBoundaryProvider : Type where
  provide :
    ∀ {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
        Boundary.StmtBoundary Γc σc body

/-- Provides reentry continuations for body-normal/body-continue while paths. -/
structure WhileReentryContinuationProvider : Type where
  bodyNormalReentry :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .normal σb →
        Σ Reentry : Prop,
          Continuation.WhileReentryContinuation Γ Γc σ σb cond body Reentry
  bodyContinueReentry :
    ∀ {Γ Γc : TypeEnv} {σ σc σb : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Boundary.CondBoundary Γ Γc σ cond →
      Semantics.BigStepCond σ cond true σc →
      Boundary.StmtBoundary Γc σc body →
      Semantics.BigStepStmt σc body .continueResult σb →
        Σ Reentry : Prop,
          Continuation.WhileReentryContinuation Γ Γc σ σb cond body Reentry

/-- Provider bundle for the while structural clause. -/
structure WhileClauseProviders : Type where
  body : WhileBodyBoundaryProvider
  reentry : WhileReentryContinuationProvider

/-- Concrete while clause from body-boundary and reentry-continuation providers. -/
def whileStructuralSoundnessClause
    (P : WhileClauseProviders) :
    Structural.WhileStructuralSoundnessClause where
  sound := by
    intro Γ σ cond body boundary bodySound reentrySound
    cases boundary with
    | mk static effect safety entry =>
        let wholeBoundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body) :=
          Boundary.StmtBoundary.mk static effect safety entry
        cases entry with
        | whileCond condition =>
            cases hvalue : condition.value with
            | false =>
                have condStep :
                    Semantics.BigStepCond σ cond false condition.post := by
                  simpa [hvalue] using condition.eval
                exact Semantic.while_false_of_condition condStep
            | true =>
                have condStep :
                    Semantics.BigStepCond σ cond true condition.post := by
                  simpa [hvalue] using condition.eval
                let bodyBoundary : Boundary.StmtBoundary _ condition.post body :=
                  P.body.provide wholeBoundary condition condStep
                have hbody : ClosedStmtSoundness condition.post body :=
                  bodySound bodyBoundary
                exact
                  Semantic.while_true_of_body_classified
                    condStep
                    hbody
                    (fun reentered =>
                      match reentered with
                      | Or.inl bodyNormal =>
                          match
                            P.reentry.bodyNormalReentry
                              wholeBoundary
                              condition
                              condStep
                              bodyBoundary
                              bodyNormal
                          with
                          | ⟨_Reentry, cont⟩ => reentrySound cont
                      | Or.inr bodyContinue =>
                          match
                            P.reentry.bodyContinueReentry
                              wholeBoundary
                              condition
                              condStep
                              bodyBoundary
                              bodyContinue
                          with
                          | ⟨_Reentry, cont⟩ => reentrySound cont)

end Instantiate
end Soundness
end Cpp3
