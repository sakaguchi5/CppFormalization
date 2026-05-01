import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI

namespace Cpp

/-!
# Closure.Foundation.BodyAdequacyWitnessCI

Compatibility aliases for the witness-provider migration.

`BodyAdequacyCI` and `BlockBodyAdequacyCI` now carry witness-producing fields in
the main records.  The `*WitnessCI` records remain as a lightweight compatibility
surface for code that was written during the migration.  The forgetful adapters
now preserve the witness fields explicitly.
-/

/--
Compatibility witness-producing version of statement-body adequacy.

New code may use `BodyAdequacyCI` directly via its `normalWitness` and
`returnWitness` fields.  This record remains useful as an explicit provider
surface where a distinct name improves readability.
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

/-- Convert a compatibility witness provider to the main adequacy record. -/
def toBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyWitnessCI Γ σ st P) :
    BodyAdequacyCI Γ σ st P :=
  BodyAdequacyCI.ofWitness A.normalWitness A.returnWitness

/-- Extract the compatibility witness provider from the main adequacy record. -/
def ofBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : BodyAdequacyCI Γ σ st P) :
    BodyAdequacyWitnessCI Γ σ st P :=
  { normalWitness := A.normalWitness
    returnWitness := A.returnWitness }

end BodyAdequacyWitnessCI

/--
Compatibility witness-producing version of opened block-body adequacy.

New code may use `BlockBodyAdequacyCI` directly via its `normalWitness` and
`returnWitness` fields.  This record remains as an explicit provider surface.
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

/-- Convert a compatibility block witness provider to the main adequacy record. -/
def toBlockBodyAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyWitnessCI Γ σ ss P) :
    BlockBodyAdequacyCI Γ σ ss P :=
  BlockBodyAdequacyCI.ofWitness A.normalWitness A.returnWitness

/-- Extract the compatibility block witness provider from the main adequacy record. -/
def ofBlockBodyAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (A : BlockBodyAdequacyCI Γ σ ss P) :
    BlockBodyAdequacyWitnessCI Γ σ ss P :=
  { normalWitness := A.normalWitness
    returnWitness := A.returnWitness }

end BlockBodyAdequacyWitnessCI

end Cpp
