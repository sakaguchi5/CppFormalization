import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlPreservation

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtNormalWitness

Phase-1 execution-based witness workbench for normal completion.

This file stays deliberately small and honest:
- it does **not** claim the global theorem
  `normal_control_witness_of_bigStep_v3`;
- it only isolates the first three normal cases that make the proof pattern
  explicit:
  `skip`, `assign`, and `seqNormal`.

The goal is to expose the intended execution-based shape:
actual normal execution -> CI normal witness -> control compatibility.
-/


/--
Execution-based normal witness package.

`out` is the CI normal witness, and `comp` says that this witness is actually
compatible with the given normal execution.
-/
structure NormalControlWitnessV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') : Type where -- Prop から Type へ
  out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  comp : StmtControlCompatible out.property hstep

namespace NormalControlWitnessV3

def end_env
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (w : NormalControlWitnessV3 (Γ := Γ) hstep) :
    TypeEnv :=
  w.out.1

@[simp] theorem typing
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (w : NormalControlWitnessV3 (Γ := Γ) hstep) :
    HasTypeStmtCI .normalK Γ st w.out.1 :=
  w.out.2

/--
Transport a normal witness package across a propositional equality of the
*start* environment.

This is where the name/binder mismatch is absorbed once and for all.
-/
def transport_start_env
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : NormalControlWitnessV3 (Γ := Γ₁) hstep) :
    NormalControlWitnessV3 (Γ := Γ₂) hstep := by
  subst hΓ
  exact w

@[simp] theorem transport_start_env_out
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : NormalControlWitnessV3 (Γ := Γ₁) hstep) :
    (transport_start_env hΓ w).out.1 = w.out.1 := by
  subst hΓ
  rfl

/-
Compose two normal witness packages through a sequential normal execution.

This is the abstraction that hides the environment-name transport noise.
-/
def seq_normal
    {Γ Θ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s t : CppStmt}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepStmt σ₁ t .normal σ₂}
    (wS : NormalControlWitnessV3 (Γ := Γ) hstepS)
    (wT : NormalControlWitnessV3 (Γ := Θ) hstepT)
    (hΘ : wS.out.1 = Θ) :
    NormalControlWitnessV3
      (Γ := Γ)
      (hstep := BigStepStmt.seqNormal hstepS hstepT) := by
  let wT' : NormalControlWitnessV3 (Γ := wS.out.1) hstepT :=
    transport_start_env hΘ.symm wT
  refine
    { out := ⟨wT'.out.1, HasTypeStmtCI.seq_normal wS.out.2 wT'.out.2⟩
      comp := ?_ }
  exact StmtControlCompatible.seq_normal wS.comp wT'.comp

@[simp] theorem seq_normal_end_env
    {Γ Θ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s t : CppStmt}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepStmt σ₁ t .normal σ₂}
    (wS : NormalControlWitnessV3 (Γ := Γ) hstepS)
    (wT : NormalControlWitnessV3 (Γ := Θ) hstepT)
    (hΘ : wS.out.1 = Θ) :
    (NormalControlWitnessV3.seq_normal wS wT hΘ).out.1 = wT.out.1 := by
  change (NormalControlWitnessV3.transport_start_env hΘ.symm wT).out.1 = wT.out.1
  simp

end NormalControlWitnessV3

/--
Your original seq-normal theorem, rewritten through the packaged abstraction.

The transport/name-management ceremony is now internalized inside
`NormalControlWitnessV3.seq_normal`.
-/
theorem seq_normal_control_witness_of_subwitnesses_v3
    {Γ Θ Δ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s t : CppStmt}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepStmt σ₁ t .normal σ₂}
    (houtS :
      ∃ outS : {Θ' : TypeEnv // HasTypeStmtCI .normalK Γ s Θ'},
        outS.1 = Θ ∧ StmtControlCompatible outS.property hstepS)
    (houtT :
      ∃ outT : {Δ' : TypeEnv // HasTypeStmtCI .normalK Θ t Δ'},
        outT.1 = Δ ∧ StmtControlCompatible outT.property hstepT) :
    ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Ξ},
      out.1 = Δ ∧
      StmtControlCompatible out.property (BigStepStmt.seqNormal hstepS hstepT) := by
  rcases houtS with ⟨outS, h_eqS, hcompS⟩
  rcases houtT with ⟨outT, h_eqT, hcompT⟩

  let wS : NormalControlWitnessV3 (Γ := Γ) hstepS :=
    { out := outS, comp := hcompS }

  let wT : NormalControlWitnessV3 (Γ := Θ) hstepT :=
    { out := outT, comp := hcompT }

  let wSeq : NormalControlWitnessV3
      (Γ := Γ)
      (hstep := BigStepStmt.seqNormal hstepS hstepT) :=
    NormalControlWitnessV3.seq_normal wS wT h_eqS

  refine ⟨wSeq.out, ?_⟩
  refine ⟨?_, wSeq.comp⟩
  calc
    wSeq.out.1 = wT.out.1 := by
      simp [ wSeq ,NormalControlWitnessV3.seq_normal_end_env]
    _ = outT.1 := rfl
    _ = Δ := h_eqT


/--
Phase-1 normal witness package:
- `skip`
- `assign`
- `seqNormal`

This is not the final global theorem. It records the first three cases where
execution-based normal witnesses are already made explicit.
-/
structure StmtNormalWitnessPhase1V3 : Type where
  skip_case :
    ∀ {Γ : TypeEnv} {σ : State}
      {hstep : BigStepStmt σ CppStmt.skip .normal σ},
      NormalControlWitnessV3 (Γ := Γ) hstep

  assign_case :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType},
      HasPlaceType Γ p τ →
      HasValueType Γ e τ →
      ∀ {hstep : BigStepStmt σ (.assign p e) .normal σ'},
        NormalControlWitnessV3 (Γ := Γ) hstep

  seq_normal_case :
    ∀ {Γ Θ : TypeEnv}
      {σ σ₁ σ₂ : State}
      {s t : CppStmt}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepStmt σ₁ t .normal σ₂},
      (wS : NormalControlWitnessV3 (Γ := Γ) hstepS) →
      (wT : NormalControlWitnessV3 (Γ := Θ) hstepT) →
      wS.out.1 = Θ →
      NormalControlWitnessV3
        (Γ := Γ)
        (hstep := BigStepStmt.seqNormal hstepS hstepT)

/-- The phase-1 package is already inhabited by the explicit constructors above. -/
def stmtNormalWitnessPhase1V3_inst : StmtNormalWitnessPhase1V3 := by
  refine
    { skip_case := ?_
      assign_case := ?_
      seq_normal_case := ?_ }

  · intro Γ σ hstep
    refine
      { out := ⟨Γ, HasTypeStmtCI.skip⟩
        comp := ?_ }
    simpa using (StmtControlCompatible.skip (Γ := Γ) (σ := σ))

  · intro Γ σ σ' p e τ hp hv hstep
    refine
      { out := ⟨Γ, HasTypeStmtCI.assign hp hv⟩
        comp := ?_ }
    simpa using
      (StmtControlCompatible.assign
        (Γ := Γ) (σ := σ) (σ' := σ')
        (hp := hp) (hv := hv) (hstep := hstep))

  · intro Γ Θ σ σ₁ σ₂ s t hstepS hstepT wS wT hΘ
    exact NormalControlWitnessV3.seq_normal wS wT hΘ

end Cpp
