import CppFormalization.Cpp2.Closure.External.TransportV3

namespace Cpp

/-!
# Closure.External.TransportPropsV3

Small transport / proof-irrelevance lemmas used by higher builder-style
boundary comparison arguments.

These are intentionally separated from `BuilderV3` so that the builder layer
keeps its main role: packaging a certificate family into the V3 external
interfaces. The lemmas here are about dependent equality bookkeeping, not
about the conceptual content of the builder itself.
-/

private theorem bodyNormalWitness_unique
    {Γ : TypeEnv} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (a b :
      { out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} //
        p.summary.normalOut = some out }) :
    a = b := by
  apply Subtype.ext
  have hsome : some a.val = some b.val :=
    a.property.symm.trans b.property
  exact Option.some.inj hsome

private theorem bodyReturnWitness_unique
    {Γ : TypeEnv} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (a b :
      { out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} //
        p.summary.returnOut = some out }) :
    a = b := by
  apply Subtype.ext
  have hsome : some a.val = some b.val :=
    a.property.symm.trans b.property
  exact Option.some.inj hsome

/-- `BodyAdequacyCI` is propositionally proof-irrelevant at a fixed profile. -/
theorem bodyAdequacy_eq
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {p : BodyControlProfile Γ st}
    (A B : BodyAdequacyCI Γ σ st p) :
    A = B := by
  cases A with
  | mk AnormalWitness AreturnWitness =>
  cases B with
  | mk BnormalWitness BreturnWitness =>
  have hNormalWitness : @AnormalWitness = @BnormalWitness := by
    funext σ' hstep
    exact bodyNormalWitness_unique
      (AnormalWitness (σ' := σ') hstep)
      (BnormalWitness (σ' := σ') hstep)
  have hReturnWitness : @AreturnWitness = @BreturnWitness := by
    funext rv σ' hstep
    exact bodyReturnWitness_unique
      (AreturnWitness (rv := rv) (σ' := σ') hstep)
      (BreturnWitness (rv := rv) (σ' := σ') hstep)
  cases hNormalWitness
  cases hReturnWitness
  rfl

end Cpp
