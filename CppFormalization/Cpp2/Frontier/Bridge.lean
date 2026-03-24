import CppFormalization.Cpp2.Frontier.SafetyAxioms

/-!
Bridge from the idealized core to observed real-program behavior.
-/

namespace Cpp

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

end Cpp
