import CppFormalization.Cpp2.All

namespace Cpp


axiom assigns_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    TypedState Γ σ →
    HasPlaceType Γ p τ →
    Assigns σ p v σ' →
    TypedState Γ σ'

axiom declares_object_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    TypedState Γ σ →
    DeclaresObject σ τ x ov σ' →
    TypedState (declareTypeObject Γ x τ) σ'

axiom declares_ref_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    TypedState Γ σ →
    DeclaresRef σ τ x a σ' →
    TypedState (declareTypeRef Γ x τ) σ'

axiom place_progress
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ →
    TypedState Γ σ →
    NoUninitPlace σ p →
    NoInvalidRefPlace σ p →
    ∃ a, BigStepPlace σ p a

axiom value_progress
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    TypedState Γ σ →
    NoUninitValue σ e →
    NoInvalidRefValue σ e →
    ∃ v, BigStepValue σ e v

axiom bigstep_preserves_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult} :
    HasTypeStmt Γ st Δ →
    TypedState Γ σ →
    BigStepStmt σ st ctrl σ' →
    TypedState Δ σ'

axiom stmt_safe_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st

axiom no_uninit_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoUninitStmt σ st ↔ NoUninitStmt σ' st

axiom no_invalid_ref_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoInvalidRefStmt σ st ↔ NoInvalidRefStmt σ' st
/-
axiom no_top_break_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    BreakWellScoped st → BigStepStmt σ st .breakResult σ' → False

axiom no_top_continue_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    ContinueWellScoped st → BigStepStmt σ st .continueResult σ' → False
-/
theorem ideal_no_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  exact stmt_safe_progress_or_diverges hfrag hassm

theorem ideal_no_unclassified_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ¬ UnclassifiedStuck σ st := by
  intro hstk
  rcases ideal_no_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm with hterm | hdiv
  · exact hstk.1 hterm
  · exact hstk.2 hdiv


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

inductive EvalResult (α : Type u) where
  | ok : α → EvalResult α
  | timeout : EvalResult α
  deriving Repr

inductive EvalClassifiedResult (α : Type u) where
  | ok : α → EvalClassifiedResult α
  | fail : SemFailure → EvalClassifiedResult α
  | timeout : EvalClassifiedResult α
  deriving Repr

axiom evalPlace : Nat → State → PlaceExpr → EvalResult Nat
axiom evalValue : Nat → State → ValExpr → EvalResult Value
axiom evalStmt : Nat → State → CppStmt → EvalClassifiedResult (CtrlResult × State)


def InEvaluatorFragment : CppStmt → Prop :=
  InBigStepFragment

axiom evalPlace_fuel_mono
    {fuel : Nat} {σ : State} {p : PlaceExpr} {a : Nat} :
    evalPlace fuel σ p = .ok a → evalPlace (fuel + 1) σ p = .ok a

axiom evalValue_fuel_mono
    {fuel : Nat} {σ : State} {e : ValExpr} {v : Value} :
    evalValue fuel σ e = .ok v → evalValue (fuel + 1) σ e = .ok v

axiom evalStmt_ok_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {res : CtrlResult × State} :
    evalStmt fuel σ st = .ok res → evalStmt (fuel + 1) σ st = .ok res

axiom evalStmt_fail_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    evalStmt fuel σ st = .fail e → evalStmt (fuel + 1) σ st = .fail e

axiom evalPlace_sound
    {fuel : Nat} {σ : State} {p : PlaceExpr} {a : Nat} :
    evalPlace fuel σ p = .ok a → BigStepPlace σ p a

axiom evalValue_sound
    {fuel : Nat} {σ : State} {e : ValExpr} {v : Value} :
    evalValue fuel σ e = .ok v → BigStepValue σ e v

axiom evalStmt_ok_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .ok (ctrl, σ') →
    BigStepStmt σ st ctrl σ'

axiom evalStmt_fail_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .fail e →
    BigStepStmtFail σ st e

axiom evalPlace_complete
    {σ : State} {p : PlaceExpr} {a : Nat} :
    BigStepPlace σ p a → ∃ fuel, evalPlace fuel σ p = .ok a

axiom evalValue_complete
    {σ : State} {e : ValExpr} {v : Value} :
    BigStepValue σ e v → ∃ fuel, evalValue fuel σ e = .ok v

axiom evalStmt_ok_complete
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, evalStmt fuel σ st = .ok (ctrl, σ')

axiom evalStmt_fail_complete
    {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    BigStepStmtFail σ st e →
    ∃ fuel, evalStmt fuel σ st = .fail e

axiom timeout_eliminated_by_sufficient_fuel
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, ∀ fuel' ≥ fuel, evalStmt fuel' σ st = .ok (ctrl, σ')

structure RealProgram where
  source : String
  deriving Repr

axiom ObservedBadBehavior : RealProgram → Prop
axiom EncodesAsIdeal : RealProgram → TypeEnv → State → CppStmt → Prop


def BridgeCorrect (real : RealProgram) (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  EncodesAsIdeal real Γ σ st


def RealCounterexample (real : RealProgram) : Prop :=
  ObservedBadBehavior real

axiom real_counterexample_requires_escape_or_bad_bridge
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    ¬ IdealAssumptions Γ σ st ∨ ¬ BridgeCorrect real Γ σ st ∨ UnclassifiedStuck σ st

theorem real_counterexample_not_internal_refutation
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    BridgeCorrect real Γ σ st →
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    False := by
  intro hreal hbridge hassm hfrag
  have hnstk := ideal_no_unclassified_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm
  rcases real_counterexample_requires_escape_or_bad_bridge (Γ := Γ) (σ := σ) (st := st) hreal with hbad | hbad | hstk
  · exact hbad hassm
  · exact hbad hbridge
  · exact hnstk hstk

structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  closedUnder : Name → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop
  preserves : Meta → TypeEnv → State → CppStmt → Prop

axiom std_fragment_preserves_ideal_boundary
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    IdealAssumptions Γ σ st

axiom reflection_fragment_preserves_core_fragment
    {R : VerifiedReflectionFragment} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    R.generates m st →
    R.preserves m Γ σ st →
    CoreBigStepFragment st

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    R.generates m st →
    R.preserves m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hclosed hgen hpres
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_preserves_core_fragment hgen hpres
  have hassm : IdealAssumptions Γ σ st :=
    std_fragment_preserves_ideal_boundary huse hclosed
  exact ideal_no_stuck hfrag hassm

end Cpp
