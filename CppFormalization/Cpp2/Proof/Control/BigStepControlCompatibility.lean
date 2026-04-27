import CppFormalization.Cpp2.Proof.Preservation.StmtControlPreservation

namespace Cpp

/-!
# Proof.Control.BigStepControlCompatibility

Correctly named public surface for synthesizing control compatibility from
big-step executions and CI typing derivations.

This is intentionally a first-stage relocation facade:
- the existing proof body still lives in
  `Proof.Preservation.StmtControlPreservation`;
- new code should import this file and use the names below;
- a later cleanup can move or shorten the underlying recursor proof without
  changing downstream theorem names.

Conceptually, these theorems are not preservation theorems.  They build
`StmtControlCompatible` / `BlockControlCompatible` witnesses from an execution
and the matching control-sensitive typing derivation.
-/

/-- Statement-level compatibility synthesis from a big-step execution. -/
theorem stmtControlCompatible_of_bigStep
    {σ : State} {s : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ s ctrl σ') :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .normalK Γ s Δ),
          StmtControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .breakK Γ s Δ),
          StmtControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeStmtCI .continueK Γ s Δ),
          StmtControlCompatible hty hstep
    | .returnResult _ => True := by
  exact stmt_compat_claim hstep

/-- Block-level compatibility synthesis from a big-step execution. -/
theorem blockControlCompatible_of_bigStep
    {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepBlock σ ss ctrl σ') :
    match ctrl with
    | .normal =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .normalK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .breakResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .breakK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .continueResult =>
        ∀ {Γ Δ : TypeEnv} (hty : HasTypeBlockCI .continueK Γ ss Δ),
          BlockControlCompatible hty hstep
    | .returnResult _ => True := by
  exact block_compat_claim hstep

/-- Convenience statement normal case. -/
theorem stmtControlCompatible_normal_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hstep : BigStepStmt σ s .normal σ')
    (hty : HasTypeStmtCI .normalK Γ s Δ) :
    StmtControlCompatible hty hstep := by
  exact stmtControlCompatible_of_bigStep hstep hty

/-- Convenience statement break case. -/
theorem stmtControlCompatible_break_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hstep : BigStepStmt σ s .breakResult σ')
    (hty : HasTypeStmtCI .breakK Γ s Δ) :
    StmtControlCompatible hty hstep := by
  exact stmtControlCompatible_of_bigStep hstep hty

/-- Convenience statement continue case. -/
theorem stmtControlCompatible_continue_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hstep : BigStepStmt σ s .continueResult σ')
    (hty : HasTypeStmtCI .continueK Γ s Δ) :
    StmtControlCompatible hty hstep := by
  exact stmtControlCompatible_of_bigStep hstep hty

/-- Convenience block normal case. -/
theorem blockControlCompatible_normal_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hstep : BigStepBlock σ ss .normal σ')
    (hty : HasTypeBlockCI .normalK Γ ss Δ) :
    BlockControlCompatible hty hstep := by
  exact blockControlCompatible_of_bigStep hstep hty

/-- Convenience block break case. -/
theorem blockControlCompatible_break_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hstep : BigStepBlock σ ss .breakResult σ')
    (hty : HasTypeBlockCI .breakK Γ ss Δ) :
    BlockControlCompatible hty hstep := by
  exact blockControlCompatible_of_bigStep hstep hty

/-- Convenience block continue case. -/
theorem blockControlCompatible_continue_of_bigStep
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hstep : BigStepBlock σ ss .continueResult σ')
    (hty : HasTypeBlockCI .continueK Γ ss Δ) :
    BlockControlCompatible hty hstep := by
  exact blockControlCompatible_of_bigStep hstep hty

end Cpp
