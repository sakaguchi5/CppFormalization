import CppFormalization.Cpp2.Proof.Preservation.StmtWhileNormalWitness

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtWhileBodyTyping

Honest factoring of the remaining `while` bottleneck.

What the current repo has already made explicit:
- statement-level normal witness packages through phase-4,
- block-level normal witness packages through phase-1,
- `whileFalse` / `whileTrueNormal` witness builders once the body-side typing
  quadruple `(hc, hN, hB, hC)` is supplied.

What is still missing is *not* another normal witness theorem.
It is the source of the body-side `break` / `continue` typings required by the
normal `while` rule.

This file therefore does not pretend to solve that bottleneck.
It only packages it honestly.
-/

/--
A typing witness for a fixed control kind, together with the information that its
end environment is the chosen `Δ`.
-/
structure StmtControlTypingAtV3
    (k : ControlKind)
    (Γ : TypeEnv) (st : CppStmt) (Δ : TypeEnv) : Type where
  out : {Δ' : TypeEnv // HasTypeStmtCI k Γ st Δ'}
  end_eq : out.1 = Δ

namespace StmtControlTypingAtV3

@[simp] theorem typing
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    (w : StmtControlTypingAtV3 k Γ st Δ) :
    HasTypeStmtCI k Γ st Δ := by
  exact HasTypeStmtCI.transport_end_env w.end_eq w.out.2

/-- Build the packaged form from a witness that already ends at `Δ`. -/
def mk'
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    (hty : HasTypeStmtCI k Γ st Δ) :
    StmtControlTypingAtV3 k Γ st Δ :=
  { out := ⟨Δ, hty⟩
    end_eq := rfl }

end StmtControlTypingAtV3

abbrev NormalControlTypingAtV3
    (Γ : TypeEnv) (st : CppStmt) (Δ : TypeEnv) :=
  StmtControlTypingAtV3 .normalK Γ st Δ

abbrev BreakControlTypingAtV3
    (Γ : TypeEnv) (st : CppStmt) (Δ : TypeEnv) :=
  StmtControlTypingAtV3 .breakK Γ st Δ

abbrev ContinueControlTypingAtV3
    (Γ : TypeEnv) (st : CppStmt) (Δ : TypeEnv) :=
  StmtControlTypingAtV3 .continueK Γ st Δ

/--
The exact body-side typing package needed by the normal `while` rule, rewritten
in the same packaged style as the witness layers.

This is the honest "remaining slot":
to use the normal `while` constructors, we still need
- normal typing at `Γ`,
- break typing at `Γ`,
- continue typing at `Γ`.
-/
structure WhileBodyTypingKitV3
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)
  normal_body : NormalControlTypingAtV3 Γ body Γ
  break_body : BreakControlTypingAtV3 Γ body Γ
  continue_body : ContinueControlTypingAtV3 Γ body Γ

namespace WhileBodyTypingKitV3

/-- Forget the packaged representation and recover the raw quadruple used by `StmtWhileNormalWitness`. -/
def toWhileNormalTyping
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileBodyTypingKitV3 Γ c body) :
    WhileNormalTypingV3 Γ c body :=
  { hc := h.hc
    hN := h.normal_body.typing
    hB := h.break_body.typing
    hC := h.continue_body.typing }

/--
The existing `whileFalse` normal witness constructor can be driven directly from
the packaged body-typing kit.
-/
def while_false_normal
    {Γ : TypeEnv} {σ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    (h : WhileBodyTypingKitV3 Γ c body) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (st := .whileStmt c body)
      (hstep := BigStepStmt.whileFalse hcond)
      Γ :=
  NormalControlWitnessAtV3.while_false_normal
    (Γ := Γ) (c := c) (body := body) (hcond := hcond)
    h.toWhileNormalTyping

/--
Likewise for the recursive normal `whileTrueNormal` constructor.
-/
def while_true_normal
    {Γ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool true)}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
    (h : WhileBodyTypingKitV3 Γ c body)
    (hin : WhileTrueNormalInputV3
      (Γ := Γ)
      (c := c) (body := body)
      (hbody := hbody) (htail := htail)) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (hstep := BigStepStmt.whileTrueNormal hcond hbody htail)
      Γ :=
  NormalControlWitnessAtV3.while_true_normal
    (Γ := Γ) (c := c) (body := body)
    (hcond := hcond) (hbody := hbody) (htail := htail)
    h.toWhileNormalTyping hin

end WhileBodyTypingKitV3

/--
Phase-5 statement normal witness package:
phase-4 plus the honest reformulation of the `while` bottleneck as a packaged
body-typing kit.
-/
structure StmtNormalWitnessPhase5V3  : Type extends StmtNormalWitnessPhase4V3 where
  while_body_typing_kit :
    ∀ {Γ : TypeEnv} {c : ValExpr} {body : CppStmt},
      WhileBodyTypingKitV3 Γ c body →
      True

/--
Phase-5 is a bookkeeping extension only:
it does not pretend to have solved the body-side `break` / `continue` problem,
it only makes the missing slot explicit in the same packaged style as the rest
of the witness layer.
-/
def stmtNormalWitnessPhase5V3_inst : StmtNormalWitnessPhase5V3 := by
  refine
    { toStmtNormalWitnessPhase4V3 := stmtNormalWitnessPhase4V3_inst
      while_body_typing_kit := ?_ }
  intro Γ c body h
  trivial

end Cpp
