import CppFormalization.Cpp2.Proof.Preservation.StmtNormalWitness
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCompatibility

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtWhileNormalWitness

Execution-based witness workbench for `while` normal completion.

After introducing `LoopBodyBoundaryCI`, the static bottleneck should no longer be
phrased as an ad-hoc standalone quadruple.  The real static input is:
- a loop-body local 4-channel profile, and
- the boolean typing of the loop condition.

This file keeps the theorem-backed `whileFalse` / `whileTrueNormal` constructors,
but re-roots their static input in `LoopBodyControlProfile`.
-/

/--
Static input needed by the normal `while` rule.

The body-side `normal / break / continue` payload is now carried by the loop-body
profile rather than by an ad-hoc standalone structure.
-/
structure WhileNormalTypingV3
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)
  bodyProfile : LoopBodyControlProfile Γ body

namespace WhileNormalTypingV3

@[simp] def hN
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    HasTypeStmtCI .normalK Γ body Γ :=
  LoopBodyControlProfile.normalTyping h.bodyProfile

@[simp] def hB
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    HasTypeStmtCI .breakK Γ body Γ :=
  LoopBodyControlProfile.breakTyping h.bodyProfile

@[simp] def hC
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    HasTypeStmtCI .continueK Γ body Γ :=
  LoopBodyControlProfile.continueTyping h.bodyProfile

/-- Constructor from the loop-body profile plus condition typing. -/
def ofLoopBodyProfile
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (P : LoopBodyControlProfile Γ body) :
    WhileNormalTypingV3 Γ c body :=
  { hc := hc, bodyProfile := P }

/-- The canonical normal typing witness for the whole `while` statement. -/
def stmtTyping
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  LoopBodyControlProfile.whileNormalTyping h.bodyProfile h.hc

/-- Old coarse typing of the loop body, recovered from the loop-body profile. -/
def bodyTyped0
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalTypingV3 Γ c body) :
    WellTypedFrom Γ body :=
  LoopBodyControlProfile.typed0 h.bodyProfile

end WhileNormalTypingV3

/--
Packaged inputs for the `whileTrueNormal` case.

Both the body execution and the tail recursive execution must end back at `Γ`.
That requirement is not accidental: it is exactly what the normal `while`
typing rule says.
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
The `whileFalse` normal witness is already constructor-shaped once the loop-body
profile and condition typing are given.
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
- the loop-body profile together with condition typing.
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
      (st := .whileStmt c body)
      (hstep := BigStepStmt.whileTrueNormal hcond hbody htail)
      Γ := by
  let hcompS' :=
    StmtControlCompatible.transport_end_env
      hin.body_witness.end_eq hin.body_witness.witness.comp
  let hcompT' :=
    StmtControlCompatible.transport_end_env
      hin.tail_witness.end_eq hin.tail_witness.witness.comp

  refine
    { witness :=
        { out := ⟨Γ, WhileNormalTypingV3.stmtTyping hw⟩
          comp := ?_ }
      end_eq := rfl }

  exact StmtControlCompatible.while_true_normal_normal
    (hc := hw.hc) (hN := hw.hN) (hB := hw.hB) (hC := hw.hC)
    (hcond := hcond)
    hcompS'
    hcompT'

end NormalControlWitnessAtV3

/-- Existential wrapper for the `whileFalse` normal case. -/
def while_false_normal_control_witness_v3
    {Γ : TypeEnv} {σ : State}
    {c : ValExpr} {body : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    (hw : WhileNormalTypingV3 Γ c body) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ},
      out.1 = Γ ∧
      StmtControlCompatible out.property (BigStepStmt.whileFalse hcond) := by
  exact
    (NormalControlWitnessAtV3.while_false_normal
      (Γ := Γ) (c := c) (body := body) (hcond := hcond) hw).to_exists

/-- Existential wrapper for the `whileTrueNormal` case. -/
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
      StmtControlCompatible out.property
        (BigStepStmt.whileTrueNormal hcond hbody htail) := by
  exact
    (NormalControlWitnessAtV3.while_true_normal
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
        StmtControlCompatible out.property
          (BigStepStmt.whileTrueNormal hcond hbody htail)

/-- Phase-4 is already inhabited by phase-3 plus the explicit `while` constructors above. -/
def stmtNormalWitnessPhase4V3_inst : StmtNormalWitnessPhase4V3 := by
  refine
    { toStmtNormalWitnessPhase3V3 := stmtNormalWitnessPhase3V3_inst
      while_false_case := ?_
      while_true_normal_case := ?_ }
  · intro Γ σ c body hw hcond
    exact
      while_false_normal_control_witness_v3
        (Γ := Γ) (σ := σ) (c := c) (body := body) (hcond := hcond) hw
  · intro Γ σ σ₁ σ₂ c body hw hcond hbody htail hin
    exact
      while_true_normal_control_witness_v3
        (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂)
        (c := c) (body := body)
        (hcond := hcond) (hbody := hbody) (htail := htail)
        hw hin

end Cpp
