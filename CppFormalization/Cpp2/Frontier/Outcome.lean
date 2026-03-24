import CppFormalization.Cpp2.Frontier.SafetyAxioms
import CppFormalization.Cpp2.Lemmas.ControlExclusion

/-!
Top-level outcome packaging and semantic classification.
-/

namespace Cpp

def CtrlToProgSuccess : CtrlResult → Option ProgSuccess
  | .normal => some .normal
  | .returnResult rv => some (.returned rv)
  | .breakResult => none
  | .continueResult => none

theorem top_level_control_not_break
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .breakResult σ') := by
  intro hassm _
  intro h
  rcases h with ⟨σ', hstep⟩
  exact no_top_break_from_scope (ideal_assumptions_inv_break_scoped hassm) hstep

theorem top_level_control_not_continue
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .continueResult σ') := by
  intro hassm _
  intro h
  rcases h with ⟨σ', hstep⟩
  exact no_top_continue_from_scope (ideal_assumptions_inv_continue_scoped hassm) hstep

/-- ケース1: 制御フローが .normal で終了した場合の成功条件の導出 -/
theorem ideal_outcome_success_normal {σ σ' : State} {st : CppStmt} {r : ProgSuccess} :
    CtrlToProgSuccess .normal = some r →
    BigStepStmt σ st .normal σ' →
    (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
    (∃ rv, r = .returned rv ∧ BigStepStmt σ st (.returnResult rv) σ') := by
  intro hcs hstep
  left
  constructor
  · -- hcs の向きを入れ替えてから simplify & apply
    simpa [CtrlToProgSuccess] using hcs.symm
  · exact hstep

/-- ケース2: 制御フローが .returnResult で終了した場合の成功条件の導出 -/
theorem ideal_outcome_success_return {σ σ' : State} {st : CppStmt} {r : ProgSuccess} {rv : Option Value} :
    CtrlToProgSuccess (.returnResult rv) = some r →
    BigStepStmt σ st (.returnResult rv) σ' →
    (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
    (∃ rv', r = .returned rv' ∧ BigStepStmt σ st (.returnResult rv') σ') := by
  intro hcs hstep
  right
  exists rv
  constructor
  · -- hcs : some (.returned rv) = some r を簡約して r = .returned rv を導く
    simp [CtrlToProgSuccess] at hcs
    exact hcs.symm
  · -- 実行ログの整合性
    exact hstep

theorem ideal_prog_outcome_exists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ∃ out : ProgOutcome,
      match out with
      | .success r σ' =>
          (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
          (∃ rv, r = .returned rv ∧ BigStepStmt σ st (.returnResult rv) σ')
      | .diverges => BigStepStmtDiv σ st := by
  rcases ideal_no_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm with hterm | hdiv
  · rcases hterm with ⟨ctrl, σ', hstep⟩
    cases hcs : CtrlToProgSuccess ctrl with
    | none =>
        cases ctrl with
        | normal => cases hcs
        | returnResult rv => cases hcs
        | breakResult =>
            exfalso
            exact top_level_control_not_break hassm hfrag ⟨σ', hstep⟩
        | continueResult =>
            exfalso
            exact top_level_control_not_continue hassm hfrag ⟨σ', hstep⟩
    | some r =>
        refine ⟨.success r σ', ?_⟩
        cases ctrl with
        | normal =>
            exact ideal_outcome_success_normal hcs hstep
        | returnResult rv =>
            exact ideal_outcome_success_return hcs hstep
        | breakResult => cases hcs
        | continueResult => cases hcs
  · exact ⟨.diverges, hdiv⟩


inductive SemFailure where
  | uninitializedRead
  | invalidDeref
  | invalidAssign
  | invalidRefBind
  | badBreak
  | badContinue
  deriving DecidableEq, Repr

inductive SemClassifiedOutcome where
  | success  : ProgSuccess → State → SemClassifiedOutcome
  | failure  : SemFailure → SemClassifiedOutcome
  | diverges : SemClassifiedOutcome
  deriving Repr

axiom BigStepStmtFail : State → CppStmt → SemFailure → Prop


def Classified (σ : State) (st : CppStmt) : Prop :=
  BigStepStmtTerminates σ st ∨ (∃ e, BigStepStmtFail σ st e) ∨ BigStepStmtDiv σ st

axiom ideal_classified
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    Classified σ st

end Cpp
