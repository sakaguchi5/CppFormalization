import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyAdequacyCI

四層分離の第4層。

ここでは control profile が actual big-step exits に対して adequate であることを述べる。
summary 自体は state-free だが、その adequacy は state / execution に依存する。
したがって profile と adequacy は別層である。

Witness-provider migration:
`BodyAdequacyCI` / `BlockBodyAdequacyCI` now carry witness-producing fields
inside the main records.  The older proof-only `normalSound` / `returnSound`
fields are retained as compatibility surfaces during the destructive migration;
when callers omit the witness fields, the default witnesses are selected from
those proof-only fields by `Classical.choose`.
-/

/-- Adequacy of a statement control profile against actual statement execution. -/
structure BodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  /-- Proof-only normal soundness, retained for compatibility. -/
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        P.summary.normalOut = some out
  /-- Proof-only return soundness, retained for compatibility. -/
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        P.summary.returnOut = some out
  /-- Witness-producing normal adequacy used by provider-facing downstream code. -/
  normalWitness :
    ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
      { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
        P.summary.normalOut = some out } := by
      intro σ' hstep
      let h := normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
  /-- Witness-producing return adequacy used by provider-facing downstream code. -/
  returnWitness :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
      { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
        P.summary.returnOut = some out } := by
      intro rv σ' hstep
      let h := returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩

namespace BodyAdequacyCI

/-- Build statement adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (normalWitness :
      ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
        { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
          P.summary.normalOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State}
        (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
        { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
          P.summary.returnOut = some out }) :
    BodyAdequacyCI Γ σ st P :=
  { normalSound := by
      intro σ' hstep
      let w := normalWitness hstep
      exact ⟨w.val, w.property⟩
    returnSound := by
      intro rv σ' hstep
      let w := returnWitness hstep
      exact ⟨w.val, w.property⟩
    normalWitness := normalWitness
    returnWitness := returnWitness }

end BodyAdequacyCI

/-- Adequacy of an opened block-body profile against actual block execution. -/
structure BlockBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  /-- Proof-only normal soundness, retained for compatibility. -/
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ},
        P.summary.normalOut = some out
  /-- Proof-only return soundness, retained for compatibility. -/
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ},
        P.summary.returnOut = some out
  /-- Witness-producing normal adequacy used by provider-facing downstream code. -/
  normalWitness :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      { out : {Δ : TypeEnv //
          HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} //
        P.summary.normalOut = some out } := by
      intro σ' hstep
      let h := normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
  /-- Witness-producing return adequacy used by provider-facing downstream code. -/
  returnWitness :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      { out : {Δ : TypeEnv //
          HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} //
        P.summary.returnOut = some out } := by
      intro rv σ' hstep
      let h := returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩

namespace BlockBodyAdequacyCI

/-- Build opened block adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (normalWitness :
      ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
        { out : {Δ : TypeEnv //
            HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} //
          P.summary.normalOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State}
        (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
        { out : {Δ : TypeEnv //
            HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} //
          P.summary.returnOut = some out }) :
    BlockBodyAdequacyCI Γ σ ss P :=
  { normalSound := by
      intro σ' hstep
      let w := normalWitness hstep
      exact ⟨w.val, w.property⟩
    returnSound := by
      intro rv σ' hstep
      let w := returnWitness hstep
      exact ⟨w.val, w.property⟩
    normalWitness := normalWitness
    returnWitness := returnWitness }

end BlockBodyAdequacyCI

end Cpp
