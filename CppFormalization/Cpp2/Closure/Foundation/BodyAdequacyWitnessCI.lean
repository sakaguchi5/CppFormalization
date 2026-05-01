import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI

namespace Cpp

/-!
# Closure.Foundation.BodyAdequacyWitnessCI

Witness-producing adequacy providers.

`BodyAdequacyCI` and `BlockBodyAdequacyCI` remain the proof-only adequacy
interfaces.  The witness-producing versions below are the non-breaking migration
layer used when downstream constructions must build Type-level packages from
actual exits.
-/

/--
Witness-producing version of statement-body adequacy.

This carries the same mathematical content as `BodyAdequacyCI`, but returns the
selected profile witness as Type-level data rather than hiding it behind a
`Prop`-level existential.
-/
structure BodyAdequacyWitnessCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  normalWitness :
    ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
      { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
        P.summary.normalOut = some out }
  returnWitness :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
      { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
        P.summary.returnOut = some out }

namespace BodyAdequacyWitnessCI

/-- Forget a witness-producing adequacy provider to ordinary proof-only adequacy. -/
def toBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyWitnessCI Γ σ st P) :
    BodyAdequacyCI Γ σ st P :=
  { normalSound := by
      intro σ' hstep
      let w := A.normalWitness hstep
      exact ⟨w.val, w.property⟩
    returnSound := by
      intro rv σ' hstep
      let w := A.returnWitness hstep
      exact ⟨w.val, w.property⟩ }

/--
Classical bridge from proof-only statement adequacy to witness-producing
adequacy.

This is intentionally noncomputable: it selects the profile output hidden behind
the `Prop`-level existential in `BodyAdequacyCI`.  Prefer theorem-backed
witness providers when available; this adapter exists for compatibility during
the migration.
-/
noncomputable def ofBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyCI Γ σ st P) :
    BodyAdequacyWitnessCI Γ σ st P :=
  { normalWitness := by
      intro σ' hstep
      let h := A.normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    returnWitness := by
      intro rv σ' hstep
      let h := A.returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩ }

end BodyAdequacyWitnessCI

/--
Witness-producing version of opened block-body adequacy.

This is the block analogue of `BodyAdequacyWitnessCI`; it is kept separate from
`BlockBodyAdequacyCI` so the current proof-only boundary interface remains
source-compatible during the migration.
-/
structure BlockBodyAdequacyWitnessCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  normalWitness :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      { out : {Δ : TypeEnv //
          HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} //
        P.summary.normalOut = some out }
  returnWitness :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      { out : {Δ : TypeEnv //
          HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} //
        P.summary.returnOut = some out }

namespace BlockBodyAdequacyWitnessCI

/-- Forget a block witness-producing adequacy provider to ordinary proof-only adequacy. -/
def toBlockBodyAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyWitnessCI Γ σ ss P) :
    BlockBodyAdequacyCI Γ σ ss P :=
  { normalSound := by
      intro σ' hstep
      let w := A.normalWitness hstep
      exact ⟨w.val, w.property⟩
    returnSound := by
      intro rv σ' hstep
      let w := A.returnWitness hstep
      exact ⟨w.val, w.property⟩ }

/--
Classical bridge from proof-only opened block adequacy to witness-producing
opened block adequacy.

As with `BodyAdequacyWitnessCI.ofBodyAdequacy`, this is a compatibility adapter
for the migration period.
-/
noncomputable def ofBlockBodyAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyCI Γ σ ss P) :
    BlockBodyAdequacyWitnessCI Γ σ ss P :=
  { normalWitness := by
      intro σ' hstep
      let h := A.normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    returnWitness := by
      intro rv σ' hstep
      let h := A.returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩ }

end BlockBodyAdequacyWitnessCI

end Cpp
