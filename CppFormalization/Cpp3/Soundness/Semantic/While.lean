import CppFormalization.Cpp3.Soundness.Semantic.Branch

/-!
# CppFormalization.Cpp3.Soundness.Semantic.While

Pure semantic propagation lemmas for while-statements.

These lemmas deliberately do not prove termination.  A loop is classified either
by a finite exit/break/return path, by divergence in the condition/body/reentry
corridor, or by a classified reentry supplied by the structural while clause.
The genuinely infinite case remains represented by `StmtDiv.whileForever` in the
semantics kernel; the structural instantiation below only needs the reentry
callback surface already exposed by `WhileStructuralSoundnessClause`.
-/

namespace Cpp3
namespace Soundness
namespace Semantic

/-- A false guard classifies a while-statement by finite normal exit. -/
theorem while_false_of_condition
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condStep : Semantics.BigStepCond σ cond false σc) :
    ClosedStmtSoundness σ (.whileStmt cond body) := by
  change Semantics.StmtClassified σ (.whileStmt cond body)
  exact Or.inl ⟨.normal, σc, Semantics.BigStepStmt.whileFalse condStep⟩

/-- Lift a classified reentry state back through one normal/continue while iteration. -/
theorem while_reentry_of_classified
    {σ σc σb : State} {cond : CppCond} {body : CppStmt}
    (condStep : Semantics.BigStepCond σ cond true σc)
    (reentered : Semantics.LoopBodyReenters σc body σb)
    (loopSound : ClosedStmtSoundness σb (.whileStmt cond body)) :
    ClosedStmtSoundness σ (.whileStmt cond body) := by
  change Semantics.StmtClassified σ (.whileStmt cond body)
  change Semantics.StmtClassified σb (.whileStmt cond body) at loopSound
  cases loopSound with
  | inr loopDiv =>
      exact Or.inr (Semantics.StmtDiv.whileReenter condStep reentered loopDiv)
  | inl loopTerm =>
      rcases loopTerm with ⟨r, σ₁, loopStep⟩
      cases reentered with
      | inl bodyNormal =>
          exact Or.inl ⟨r, σ₁,
            Semantics.BigStepStmt.whileBodyNormal condStep bodyNormal loopStep⟩
      | inr bodyContinue =>
          exact Or.inl ⟨r, σ₁,
            Semantics.BigStepStmt.whileBodyContinue condStep bodyContinue loopStep⟩

/--
Classify a while-statement after a true guard from the classified body and the
classified normal/continue reentry callbacks.
-/
theorem while_true_of_body_classified
    {σ σc : State} {cond : CppCond} {body : CppStmt}
    (condStep : Semantics.BigStepCond σ cond true σc)
    (bodySound : ClosedStmtSoundness σc body)
    (reentrySound :
      ∀ {σb : State},
        Semantics.LoopBodyReenters σc body σb →
          ClosedStmtSoundness σb (.whileStmt cond body)) :
    ClosedStmtSoundness σ (.whileStmt cond body) := by
  change Semantics.StmtClassified σ (.whileStmt cond body)
  change Semantics.StmtClassified σc body at bodySound
  cases bodySound with
  | inr bodyDiv =>
      exact Or.inr (Semantics.StmtDiv.whileBody condStep bodyDiv)
  | inl bodyTerm =>
      rcases bodyTerm with ⟨r, σb, bodyStep⟩
      cases r with
      | normal =>
          exact
            while_reentry_of_classified
              condStep
              (Or.inl bodyStep)
              (reentrySound (Or.inl bodyStep))
      | breakResult =>
          exact Or.inl ⟨.normal, σb,
            Semantics.BigStepStmt.whileBodyBreak condStep bodyStep⟩
      | continueResult =>
          exact
            while_reentry_of_classified
              condStep
              (Or.inr bodyStep)
              (reentrySound (Or.inr bodyStep))
      | returnResult ov =>
          exact Or.inl ⟨.returnResult ov, σb,
            Semantics.BigStepStmt.whileBodyReturn condStep bodyStep⟩

end Semantic
end Soundness
end Cpp3
