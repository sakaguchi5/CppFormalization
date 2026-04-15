import CppFormalization.Cpp2.Lemmas.ExprDeterminism
import CppFormalization.Cpp2.Lemmas.TransitionDeterminism
import CppFormalization.Cpp2.Static.NoDeclareObj

namespace Cpp

mutual

theorem bigStepStmt_deterministic_noDeclareObj
    {σ : State} {s : CppStmt} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjStmt s)
    (h₁ : BigStepStmt σ s ctrl₁ σ₁)
    (h₂ : BigStepStmt σ s ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ ∧ σ₁ = σ₂ := by
  match h₁ with
  | .skip =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .expr hv₁ =>
      cases h₂ with
      | expr hv₂ =>
          have _ := bigStepValue_deterministic hv₁ hv₂
          exact ⟨rfl, rfl⟩

  | .assign hv₁ ha₁ =>
      cases h₂ with
      | assign hv₂ ha₂ =>
          have hv : _ := bigStepValue_deterministic hv₁ hv₂
          subst hv
          exact ⟨rfl, assigns_deterministic ha₁ ha₂⟩

  | .declareObjNone _ =>
      cases hno

  | .declareObjSome _ _ =>
      cases hno

  | .declareRef hp₁ hr₁ =>
      cases h₂ with
      | declareRef hp₂ hr₂ =>
          have hp : _ := bigStepPlace_deterministic hp₁ hp₂
          subst hp
          exact ⟨rfl, declaresRef_deterministic hr₁ hr₂⟩

  | .seqNormal hs₁ ht₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              subst hσS
              rcases bigStepStmt_deterministic_noDeclareObj hnoT ht₁ ht₂ with ⟨hcT, hσT⟩
              exact ⟨hcT, hσT⟩
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqBreak hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqContinue hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS

  | .seqReturn hs₁ =>
      cases hno with
      | seq hnoS hnoT =>
          cases h₂ with
          | seqNormal hs₂ ht₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, _⟩
              cases hcS
          | seqReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcS, hσS⟩
              cases hcS
              exact ⟨rfl, hσS⟩

  | .iteTrue hv₁ hs₁ =>
      cases hno with
      | ite hnoS hnoT =>
          cases h₂ with
          | iteTrue hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hctrl, hσ⟩
              exact ⟨hctrl, hσ⟩
          | iteFalse hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc

  | .iteFalse hv₁ hs₁ =>
      cases hno with
      | ite hnoS hnoT =>
          cases h₂ with
          | iteTrue hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | iteFalse hv₂ hs₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoT hs₁ hs₂ with ⟨hctrl, hσ⟩
              exact ⟨hctrl, hσ⟩

  | .whileFalse hv₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              exact ⟨rfl, rfl⟩
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc

  | .whileTrueNormal hv₁ hb₁ hw₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              rcases bigStepStmt_deterministic_noDeclareObj (.whileStmt hnoBody) hw₁ hw₂ with ⟨hcw, hσw⟩
              exact ⟨hcw, hσw⟩
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueBreak hv₁ hb₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              exact ⟨rfl, hσb⟩
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueContinue hv₁ hb₁ hw₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              rcases bigStepStmt_deterministic_noDeclareObj (.whileStmt hnoBody) hw₁ hw₂ with ⟨hcw, hσw⟩
              exact ⟨hcw, hσw⟩
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb

  | .whileTrueReturn hv₁ hb₁ =>
      cases hno with
      | whileStmt hnoBody =>
          cases h₂ with
          | whileFalse hv₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              cases hc
          | whileTrueNormal hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueBreak hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueContinue hv₂ hb₂ hw₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, _⟩
              cases hcb
          | whileTrueReturn hv₂ hb₂ =>
              have hc : _ := bigStepValue_deterministic hv₁ hv₂
              rcases bigStepStmt_deterministic_noDeclareObj hnoBody hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              exact ⟨rfl, hσb⟩

  | .block ho₁ hb₁ hc₁ =>
      cases hno with
      | block hnoB =>
          cases h₂ with
          | block ho₂ hb₂ hc₂ =>
              have hOpen : _ := openScope_deterministic ho₁ ho₂
              subst hOpen
              rcases bigStepBlock_deterministic_noDeclareObj hnoB hb₁ hb₂ with ⟨hcb, hσb⟩
              cases hcb
              subst hσb
              exact ⟨rfl, closeScope_deterministic hc₁ hc₂⟩

  | .breakStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .continueStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .returnNoneStmt =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .returnSome hv₁ =>
      cases h₂ with
      | returnSome hv₂ =>
          have hv : _ := bigStepValue_deterministic hv₁ hv₂
          subst hv
          exact ⟨rfl, rfl⟩

theorem bigStepBlock_deterministic_noDeclareObj
    {σ : State} {ss : StmtBlock} {ctrl₁ ctrl₂ : CtrlResult} {σ₁ σ₂ : State}
    (hno : NoDeclareObjBlock ss)
    (h₁ : BigStepBlock σ ss ctrl₁ σ₁)
    (h₂ : BigStepBlock σ ss ctrl₂ σ₂) :
    ctrl₁ = ctrl₂ ∧ σ₁ = σ₂ := by
  match h₁ with
  | .nil =>
      cases h₂
      exact ⟨rfl, rfl⟩

  | .consNormal hs₁ hb₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              subst hσs
              rcases bigStepBlock_deterministic_noDeclareObj hnoB hb₁ hb₂ with ⟨hcb, hσb⟩
              exact ⟨hcb, hσb⟩
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consBreak hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consContinue hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs

  | .consReturn hs₁ =>
      cases hno with
      | cons hnoS hnoB =>
          cases h₂ with
          | consNormal hs₂ hb₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consBreak hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consContinue hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, _⟩
              cases hcs
          | consReturn hs₂ =>
              rcases bigStepStmt_deterministic_noDeclareObj hnoS hs₁ hs₂ with ⟨hcs, hσs⟩
              cases hcs
              exact ⟨rfl, hσs⟩

end

end Cpp
