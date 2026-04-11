import CppFormalization.Cpp2.Proof.Preservation.StmtNormalWitness

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtWhileNormalWitness

Execution-based witness workbench for `while` normal completion.

After reading the current statement/block witness layers carefully, the next real
bottleneck is `while`. The reason is structural:

- `seq` only needed a normal witness for the left statement and an arbitrary
  witness for the tail.
- `if` only needed one executed-branch witness plus typing data for the
  non-executed branch.
- `while` is different: even the *normal* typing rule already requires
  **three** body-side typing ingredients:
  `normal`, `break`, and `continue`.  The compatibility kernel mirrors that:
  `while_false_normal` and `while_true_normal_normal` both depend on the same
  quadruple `(hc, hN, hB, hC)`. citeturn596731view0turn596731view1

So this file does not pretend to have solved the global theorem either.
It isolates the honest helper packages for the two theorem-backed normal `while`
cases:
- `whileFalse`
- `whileTrueNormal`
-/

/--
The exact body-side typing package required by the normal `while` rule.

This is the new bottleneck that becomes visible only after statement and block
normal witnesses have been packaged honestly.
-/
structure WhileNormalTypingV3
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)
  hN : HasTypeStmtCI .normalK Γ body Γ
  hB : HasTypeStmtCI .breakK Γ body Γ
  hC : HasTypeStmtCI .continueK Γ body Γ

namespace WhileNormalTypingV3

/-- The canonical normal typing witness for the whole `while` statement. -/
def stmtTyping
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  HasTypeStmtCI.while_normal h.hc h.hN h.hB h.hC

end WhileNormalTypingV3

/--
Packaged inputs for the `whileTrueNormal` case.

Both the body execution and the tail recursive execution must end back at `Γ`.
That requirement is not accidental: it is exactly what the normal `while`
typing rule says. citeturn596731view1turn596731view0
-/
structure WhileTrueNormalInputV3
    {Γ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂} : Type where
  body_witness : NormalControlWitnessAtV3 (Γ := Γ) hbody Γ
  tail_witness : NormalControlWitnessAtV3 (Γ := Γ) htail Γ

namespace NormalControlWitnessAtV3

/--
The `whileFalse` normal witness is already constructor-shaped once the body-side
typing package is given.
-/
def while_false_normal
    {Γ : TypeEnv} {σ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    (hw : WhileNormalTypingV3 Γ c body) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (st := .whileStmt c body)
      (hstep := BigStepStmt.whileFalse hcond)
      Γ := by
  refine
    { witness :=
        { out := ⟨Γ, WhileNormalTypingV3.stmtTyping hw⟩
          comp := ?_ }
      end_eq := rfl }
  exact StmtControlCompatible.while_false_normal
    (hc := hw.hc) (hN := hw.hN) (hB := hw.hB) (hC := hw.hC)
    (hcond := hcond)

/--
The `whileTrueNormal` case is the first genuinely recursive normal `while` case.

It needs:
- the body execution packaged as a normal witness ending at `Γ`,
- the tail recursive execution packaged as a normal witness ending at `Γ`,
- the body-side typing package `(hc, hN, hB, hC)`.
-/
def while_true_normal
    {Γ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool true)}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
    (hw : WhileNormalTypingV3 Γ c body)
    (hin : WhileTrueNormalInputV3
      (Γ := Γ)
      (c := c) (body := body)
      (hbody := hbody) (htail := htail)) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (st := .whileStmt c body) -- 以前と同様に st を明示
      (hstep := BigStepStmt.whileTrueNormal hcond hbody htail)
      Γ := by
  -- 1. body の witness を hw.hN の型に transport する
  let hcompS' := StmtControlCompatible.transport_end_env hin.body_witness.end_eq hin.body_witness.witness.comp

  -- 2. tail (再帰呼び出し) の witness を while 本体の型付けに transport する
  let hcompT' := StmtControlCompatible.transport_end_env hin.tail_witness.end_eq hin.tail_witness.witness.comp

  refine
    { witness :=
        { out := ⟨Γ, WhileNormalTypingV3.stmtTyping hw⟩
          comp := ?_ }
      end_eq := rfl }

  -- 3. 型が揃った証拠を適用する
  exact StmtControlCompatible.while_true_normal_normal
    (hc := hw.hc) (hN := hw.hN) (hB := hw.hB) (hC := hw.hC)
    (hcond := hcond)
    hcompS'
    hcompT'

end NormalControlWitnessAtV3

/--
Existential wrapper for the `whileFalse` normal case.
-/
def while_false_normal_control_witness_v3
    {Γ : TypeEnv} {σ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    (hw : WhileNormalTypingV3 Γ c body) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ},
      out.1 = Γ ∧
      StmtControlCompatible out.property (BigStepStmt.whileFalse hcond) := by
  exact (NormalControlWitnessAtV3.while_false_normal (Γ := Γ) (c := c) (body := body) (hcond := hcond) hw).to_exists

/--
Existential wrapper for the `whileTrueNormal` case.
-/
def while_true_normal_control_witness_v3
    {Γ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool true)}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
    (hw : WhileNormalTypingV3 Γ c body)
    (hin : WhileTrueNormalInputV3
      (Γ := Γ)
      (c := c) (body := body)
      (hbody := hbody) (htail := htail)) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ},
      out.1 = Γ ∧
      StmtControlCompatible out.property (BigStepStmt.whileTrueNormal hcond hbody htail) := by
  exact (NormalControlWitnessAtV3.while_true_normal
    (Γ := Γ) (c := c) (body := body)
    (hcond := hcond) (hbody := hbody) (htail := htail)
    hw hin).to_exists

/--
Phase-4 statement normal witness package:
phase-3 plus the two theorem-backed normal `while` cases.
-/
structure StmtNormalWitnessPhase4V3 : Type extends StmtNormalWitnessPhase3V3 where
  while_false_case :
    ∀ {Γ : TypeEnv} {σ : State}
      {c : ValExpr} {body : CppStmt},
      WhileNormalTypingV3 Γ c body →
      ∀ {hcond : BigStepValue σ c (.bool false)},
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ},
          out.1 = Γ ∧
          StmtControlCompatible out.property (BigStepStmt.whileFalse hcond)

  while_true_normal_case :
    ∀ {Γ : TypeEnv}
      {σ σ₁ σ₂ : State}
      {c : ValExpr} {body : CppStmt},
      WhileNormalTypingV3 Γ c body →
      ∀ {hcond : BigStepValue σ c (.bool true)}
        {hbody : BigStepStmt σ body .normal σ₁}
        {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂},
      WhileTrueNormalInputV3
        (Γ := Γ)
        (c := c) (body := body)
        (hbody := hbody) (htail := htail) →
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ},
        out.1 = Γ ∧
        StmtControlCompatible out.property (BigStepStmt.whileTrueNormal hcond hbody htail)

/-- Phase-4 is already inhabited by phase-3 plus the explicit `while` constructors above. -/
def stmtNormalWitnessPhase4V3_inst : StmtNormalWitnessPhase4V3 := by
  refine
    { toStmtNormalWitnessPhase3V3 := stmtNormalWitnessPhase3V3_inst
      while_false_case := ?_
      while_true_normal_case := ?_ }
  · intro Γ σ c body hw hcond
    exact while_false_normal_control_witness_v3 (Γ := Γ) (σ := σ) (c := c) (body := body) (hcond := hcond) hw
  · intro Γ σ σ₁ σ₂ c body hw hcond hbody htail hin
    exact while_true_normal_control_witness_v3
      (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂)
      (c := c) (body := body)
      (hcond := hcond) (hbody := hbody) (htail := htail)
      hw hin

end Cpp
