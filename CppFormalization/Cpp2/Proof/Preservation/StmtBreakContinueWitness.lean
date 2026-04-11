import CppFormalization.Cpp2.Proof.Preservation.StmtAbruptWitness
import CppFormalization.Cpp2.Proof.Preservation.StmtWhileBodyTyping

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtBreakContinueWitness

Honest packaging of the remaining `break` / `continue` bottleneck.

This file does **not** pretend that `break` / `continue` witnesses are already
derivable from the current repo.
Instead it makes the missing source explicit in the same packaged style as the
normal witness layer.

The key point is this:
`while` does not really need "more normal theorems".
It needs a source of body-side
- `breakK` typing at `Γ`
- `continueK` typing at `Γ`

So the right next object is not another normal witness theorem, but an explicit
package of abrupt witness/typing sources.
-/



namespace StmtControlTypingAtV3



/-- Forget the execution witness and keep only the packaged typing witness. -/
def ofWitness
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (w : StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ) :
    StmtControlTypingAtV3 k Γ st Δ :=
  { out := w.witness.out
    end_eq := w.end_eq }

end StmtControlTypingAtV3

/--
The exact abrupt typing package needed by `while` beyond the normal body typing.
-/
structure BreakContinueTypingKitV3
    (Γ : TypeEnv) (body : CppStmt) (ΔB ΔC : TypeEnv) : Type where
  break_body : BreakControlTypingAtV3 Γ body ΔB
  continue_body : ContinueControlTypingAtV3 Γ body ΔC

namespace BreakContinueTypingKitV3

/--
The `while`-oriented specialization:
both abrupt exits come back to `Γ`.
-/
abbrev ClosedAtStart
    (Γ : TypeEnv) (body : CppStmt) :=
  BreakContinueTypingKitV3 Γ body Γ Γ

/--
Combine:
- condition typing,
- normal body typing at `Γ`,
- abrupt body typings at `Γ`,
into the exact `WhileBodyTypingKitV3` required by the normal `while` builders.
-/
def toWhileBodyTypingKit
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (hn : NormalControlTypingAtV3 Γ body Γ)
    (ha : ClosedAtStart Γ body) :
    WhileBodyTypingKitV3 Γ c body :=
  { hc := hc
    normal_body := hn
    break_body := ha.break_body
    continue_body := ha.continue_body }

end BreakContinueTypingKitV3

namespace CtrlResult

/-- 実行結果 (CtrlResult) を型付けの分類 (ControlKind) に変換する
    絶対にここにおいてはいけないし、また別の類似した定義がある可能性がある。
-/
def toKind : CtrlResult → ControlKind
  | .normal         => .normalK
  | .breakResult    => .breakK
  | .continueResult => .continueK
  | .returnResult _ => .returnK

end CtrlResult

/--
The honest remaining source of abrupt execution-based witnesses.

This is the real next theorem slot.
It is *not* yet derivable from the current repo structure.
-/
structure AbruptTypingSourceV3
    (Γ : TypeEnv) (st : CppStmt) : Type where
  break_from_execution :
    ∀ {σ : State} {ctrl : CtrlResult} {σ' : State}
      (hstep : BigStepStmt σ st ctrl σ'),
      ctrl.toKind = ControlKind.breakK →
      BreakControlWitnessAtV3 (Γ := Γ) hstep Γ
  continue_from_execution :
    ∀ {σ : State} {ctrl : CtrlResult} {σ' : State}
      (hstep : BigStepStmt σ st ctrl σ'),
      ctrl.toKind = ControlKind.continueK →
      ContinueControlWitnessAtV3 (Γ := Γ) hstep Γ

namespace AbruptTypingSourceV3

/-- Extract the closed-at-start abrupt typing kit from an abrupt typing source. -/
def toBreakContinueTypingKit
    {Γ : TypeEnv} {body : CppStmt}
    (S : AbruptTypingSourceV3 Γ body)
    {σB : State} {ctrlB : CtrlResult} {σB' : State}
    {σC : State} {ctrlC : CtrlResult} {σC' : State}
    (hbreak : BigStepStmt σB body ctrlB σB')
    (hcontinue : BigStepStmt σC body ctrlC σC')
    (hkB : ctrlB.toKind = .breakK)
    (hkC : ctrlC.toKind = .continueK) :
    BreakContinueTypingKitV3.ClosedAtStart Γ body :=
  { break_body := StmtControlTypingAtV3.ofWitness (S.break_from_execution hbreak hkB)
    continue_body := StmtControlTypingAtV3.ofWitness (S.continue_from_execution hcontinue hkC) }

end AbruptTypingSourceV3

/--
Phase-1 abrupt witness package:
we now know the exact *shape* of the missing abrupt source.
-/
structure StmtBreakContinueWitnessPhase1V3 : Type where
  abrupt_source :
    ∀ {Γ : TypeEnv} {body : CppStmt},
      AbruptTypingSourceV3 Γ body →
      True

/--
Phase-1 is intentionally bookkeeping-only:
the point is to expose the real missing slot, not to pretend it is already
solved.
-/
def stmtBreakContinueWitnessPhase1V3_inst : StmtBreakContinueWitnessPhase1V3 := by
  refine
    { abrupt_source := ?_ }
  intro Γ body S
  trivial

end Cpp
