import CppFormalization.Cpp2.Frontier.Outcome

universe u

/-!
Fuel-based evaluator interface and its soundness/completeness frontier.
-/

namespace Cpp

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

end Cpp
