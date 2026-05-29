import CppFormalization.Cpp2.Profile.LoopBody.ProfileCI
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Static.Typing.ControlIndexed

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.LoopBody.AdequacyCI

Adequacy of a loop-body four-channel profile against actual statement
execution.

The primitive fields are witness-producing.  The historical projection names
`normalSound` / `breakSound` / `continueSound` / `returnSound` are kept as record
fields for source compatibility, but new code should prefer the namespace aliases
`normalWitness` / `breakWitness` / `continueWitness` / `returnWitness`.
-/

/--
Adequacy of a loop-body 4-channel profile against actual statement execution.
-/
structure LoopBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (body : CppStmt)
    (P : LoopBodyControlProfile Γ body) : Type where
  normalSound :
    ∀ {σ' : State},
      BigStepStmt σ body .normal σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
          P.summary.normalOut = some out }

  breakSound :
    ∀ {σ' : State},
      BigStepStmt σ body .breakResult σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
          P.summary.breakOut = some out }

  continueSound :
    ∀ {σ' : State},
      BigStepStmt σ body .continueResult σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
          P.summary.continueOut = some out }

  returnSound :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ body (.returnResult rv) σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
          P.summary.returnOut = some out }

namespace LoopBodyAdequacyCI

/-- Witness-producing normal adequacy, preferred name for new code. -/
def normalWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .normal σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
      P.summary.normalOut = some out } :=
  A.normalSound hstep

/-- Witness-producing break adequacy, preferred name for new code. -/
def breakWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .breakResult σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
      P.summary.breakOut = some out } :=
  A.breakSound hstep

/-- Witness-producing continue adequacy, preferred name for new code. -/
def continueWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .continueResult σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
      P.summary.continueOut = some out } :=
  A.continueSound hstep

/-- Witness-producing return adequacy, preferred name for new code. -/
def returnWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
      P.summary.returnOut = some out } :=
  A.returnSound hstep

/-- Proof-only normal soundness recovered from the witness provider. -/
theorem normalSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ},
      P.summary.normalOut = some out := by
  let w := A.normalWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only break soundness recovered from the witness provider. -/
theorem breakSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .breakResult σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ},
      P.summary.breakOut = some out := by
  let w := A.breakWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only continue soundness recovered from the witness provider. -/
theorem continueSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {σ' : State}
    (hstep : BigStepStmt σ body .continueResult σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ},
      P.summary.continueOut = some out := by
  let w := A.continueWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only return soundness recovered from the witness provider. -/
theorem returnSoundExists
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (A : LoopBodyAdequacyCI Γ σ body P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ body (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
      P.summary.returnOut = some out := by
  let w := A.returnWitness hstep
  exact ⟨w.val, w.property⟩

/-- Build loop-body adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (normalWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .normal σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ} //
            P.summary.normalOut = some out })
    (breakWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .breakResult σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ} //
            P.summary.breakOut = some out })
    (continueWitness :
      ∀ {σ' : State},
        BigStepStmt σ body .continueResult σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ} //
            P.summary.continueOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ body (.returnResult rv) σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} //
            P.summary.returnOut = some out }) :
    LoopBodyAdequacyCI Γ σ body P :=
  { normalSound := normalWitness
    breakSound := breakWitness
    continueSound := continueWitness
    returnSound := returnWitness }

/--
Build loop-body adequacy from the old proof-only surfaces.

This is intentionally `noncomputable`: it uses classical choice to convert
proof-only existentials into subtype witnesses.  New code should prefer
`ofWitness`; this helper is only for migration.
-/
noncomputable def ofSound
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (normalSound :
      ∀ {σ' : State},
        BigStepStmt σ body .normal σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ},
            P.summary.normalOut = some out)
    (breakSound :
      ∀ {σ' : State},
        BigStepStmt σ body .breakResult σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ},
            P.summary.breakOut = some out)
    (continueSound :
      ∀ {σ' : State},
        BigStepStmt σ body .continueResult σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ},
            P.summary.continueOut = some out)
    (returnSound :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ body (.returnResult rv) σ' →
          ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
            P.summary.returnOut = some out) :
    LoopBodyAdequacyCI Γ σ body P :=
  { normalSound := by
      intro σ' hstep
      let h := normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    breakSound := by
      intro σ' hstep
      let h := breakSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    continueSound := by
      intro σ' hstep
      let h := continueSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    returnSound := by
      intro rv σ' hstep
      let h := returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩ }

end LoopBodyAdequacyCI

end Cpp
