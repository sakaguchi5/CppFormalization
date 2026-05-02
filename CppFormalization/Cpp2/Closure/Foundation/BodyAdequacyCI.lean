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

Witness-provider finalization:
`BodyAdequacyCI` / `BlockBodyAdequacyCI` now carry only witness-producing fields
as primitive data.  The older proof-only `normalSound` / `returnSound` surfaces
are derived namespace theorems.
-/

/-- Adequacy of a statement control profile against actual statement execution. -/
structure BodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  normalWitness :
    ∀ {σ' : State},
      BigStepStmt σ st .normal σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
          P.summary.normalOut = some out }

  returnWitness :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ st (.returnResult rv) σ' →
        { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
          P.summary.returnOut = some out }

namespace BodyAdequacyCI

/-- Proof-only normal soundness derived from the primitive witness provider. -/
theorem normalSound
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyCI Γ σ st P)
    {σ' : State} (hstep : BigStepStmt σ st .normal σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      P.summary.normalOut = some out := by
  let w := A.normalWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only return soundness derived from the primitive witness provider. -/
theorem returnSound
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyCI Γ σ st P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepStmt σ st (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      P.summary.returnOut = some out := by
  let w := A.returnWitness hstep
  exact ⟨w.val, w.property⟩

/-- Build statement adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (normalWitness :
      ∀ {σ' : State},
        BigStepStmt σ st .normal σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
            P.summary.normalOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ st (.returnResult rv) σ' →
          { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
            P.summary.returnOut = some out }) :
    BodyAdequacyCI Γ σ st P :=
  { normalWitness := normalWitness
    returnWitness := returnWitness }

end BodyAdequacyCI

/-- Adequacy of an opened block-body profile against actual block execution. -/
structure BlockBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  normalWitness :
    ∀ {σ' : State},
      BigStepBlock σ ss .normal σ' →
        { out : {Δ : TypeEnv //
            HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} //
          P.summary.normalOut = some out }

  returnWitness :
    ∀ {rv : Option Value} {σ' : State},
      BigStepBlock σ ss (.returnResult rv) σ' →
        { out : {Δ : TypeEnv //
            HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} //
          P.summary.returnOut = some out }

namespace BlockBodyAdequacyCI

/-- Proof-only opened-block normal soundness derived from the witness provider. -/
theorem normalSound
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyCI Γ σ ss P)
    {σ' : State} (hstep : BigStepBlock σ ss .normal σ') :
    ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ},
      P.summary.normalOut = some out := by
  let w := A.normalWitness hstep
  exact ⟨w.val, w.property⟩

/-- Proof-only opened-block return soundness derived from the witness provider. -/
theorem returnSound
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyCI Γ σ ss P)
    {rv : Option Value} {σ' : State}
    (hstep : BigStepBlock σ ss (.returnResult rv) σ') :
    ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ},
      P.summary.returnOut = some out := by
  let w := A.returnWitness hstep
  exact ⟨w.val, w.property⟩

/-- Build opened block adequacy from primitive witness-producing fields. -/
def ofWitness
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (normalWitness :
      ∀ {σ' : State},
        BigStepBlock σ ss .normal σ' →
          { out : {Δ : TypeEnv //
              HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} //
            P.summary.normalOut = some out })
    (returnWitness :
      ∀ {rv : Option Value} {σ' : State},
        BigStepBlock σ ss (.returnResult rv) σ' →
          { out : {Δ : TypeEnv //
              HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} //
            P.summary.returnOut = some out }) :
    BlockBodyAdequacyCI Γ σ ss P :=
  { normalWitness := normalWitness
    returnWitness := returnWitness }

end BlockBodyAdequacyCI

end Cpp
