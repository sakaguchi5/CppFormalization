import CppFormalization.Cpp2.Proof.Preservation.StmtNormalWitness

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtBlockNormalWitness

Execution-based witness workbench for block-body normal completion.

Position in the decomposition:
- `StmtNormalWitness.lean` now covers statement-level normal witnesses through
  atomic cases, `seqNormal`, and `if` true/false normal.
- The next honest layer is block bodies.
- This file therefore introduces the block analogue of
  `NormalControlWitnessV3`, together with the first two fundamental
  constructors:
  * `nil`
  * `cons_normal`

It also gives the bridge from a normal block-body witness to a normal statement
witness for `.block ss`, using the existing `StmtControlCompatible.block`
constructor.
-/

/--
Execution-based normal witness package for block bodies.

`out` is the CI normal block witness, and `comp` says that this witness is
actually compatible with the given normal block execution.
-/
structure BlockNormalControlWitnessV3
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} {σ' : State}
    (hstep : BigStepBlock σ ss .normal σ') : Type where
  out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ ss Δ}
  comp : BlockControlCompatible out.property hstep

namespace BlockNormalControlWitnessV3

def end_env
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} {σ' : State}
    {hstep : BigStepBlock σ ss .normal σ'}
    (w : BlockNormalControlWitnessV3 (Γ := Γ) hstep) :
    TypeEnv :=
  w.out.1

@[simp] theorem typing
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} {σ' : State}
    {hstep : BigStepBlock σ ss .normal σ'}
    (w : BlockNormalControlWitnessV3 (Γ := Γ) hstep) :
    HasTypeBlockCI .normalK Γ ss w.out.1 :=
  w.out.2

/--
Transport a normal block witness package across a propositional equality of the
*start* environment.
-/
def transport_start_env
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {ss : StmtBlock} {σ' : State}
    {hstep : BigStepBlock σ ss .normal σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : BlockNormalControlWitnessV3 (Γ := Γ₁) hstep) :
    BlockNormalControlWitnessV3 (Γ := Γ₂) hstep := by
  subst hΓ
  exact w

@[simp] theorem transport_start_env_out
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {ss : StmtBlock} {σ' : State}
    {hstep : BigStepBlock σ ss .normal σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : BlockNormalControlWitnessV3 (Γ := Γ₁) hstep) :
    (transport_start_env hΓ w).out.1 = w.out.1 := by
  subst hΓ
  rfl

/-- The empty block body already has a canonical normal witness package. -/
def nil
    {Γ : TypeEnv} {σ : State} :
    BlockNormalControlWitnessV3 (Γ := Γ) (hstep := BigStepBlock.nil (σ := σ)) := by
  refine
    { out := ⟨Γ, HasTypeBlockCI.nil⟩
      comp := ?_ }
  -- Γ と σ を明示的に渡す
  exact BlockControlCompatible.nil (Γ := Γ) (σ := σ)

/--
Compose a statement-level normal witness with a block-level normal witness
through a `consNormal` block execution.

This is the block analogue of `NormalControlWitnessV3.seq_normal`.
-/
def cons_normal
    {Γ Θ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepBlock σ₁ ss .normal σ₂}
    (wS : NormalControlWitnessV3 (Γ := Γ) hstepS)
    (wT : BlockNormalControlWitnessV3 (Γ := Θ) hstepT)
    (hΘ : wS.out.1 = Θ) :
    BlockNormalControlWitnessV3
      (Γ := Γ)
      (hstep := BigStepBlock.consNormal hstepS hstepT) := by
  let wT' : BlockNormalControlWitnessV3 (Γ := wS.out.1) hstepT :=
    transport_start_env hΘ.symm wT
  refine
    { out := ⟨wT'.out.1, HasTypeBlockCI.cons_normal wS.out.2 wT'.out.2⟩
      comp := ?_ }
  exact BlockControlCompatible.cons_normal wS.comp wT'.comp

@[simp] theorem cons_normal_end_env
    {Γ Θ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepBlock σ₁ ss .normal σ₂}
    (wS : NormalControlWitnessV3 (Γ := Γ) hstepS)
    (wT : BlockNormalControlWitnessV3 (Γ := Θ) hstepT)
    (hΘ : wS.out.1 = Θ) :
    (BlockNormalControlWitnessV3.cons_normal wS wT hΘ).out.1 = wT.out.1 := by
  change (BlockNormalControlWitnessV3.transport_start_env hΘ.symm wT).out.1 = wT.out.1
  simp

end BlockNormalControlWitnessV3

/--
The existential version of `cons_normal`, in the same style used earlier for
statement sequences.
-/
theorem cons_normal_block_control_witness_of_subwitnesses_v3
    {Γ Θ Δ : TypeEnv}
    {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock}
    {hstepS : BigStepStmt σ s .normal σ₁}
    {hstepT : BigStepBlock σ₁ ss .normal σ₂}
    (houtS :
      ∃ outS : {Θ' : TypeEnv // HasTypeStmtCI .normalK Γ s Θ'},
        outS.1 = Θ ∧ StmtControlCompatible outS.property hstepS)
    (houtT :
      ∃ outT : {Δ' : TypeEnv // HasTypeBlockCI .normalK Θ ss Δ'},
        outT.1 = Δ ∧ BlockControlCompatible outT.property hstepT) :
    ∃ out : {Ξ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Ξ},
      out.1 = Δ ∧
      BlockControlCompatible out.property (BigStepBlock.consNormal hstepS hstepT) := by
  rcases houtS with ⟨outS, h_eqS, hcompS⟩
  rcases houtT with ⟨outT, h_eqT, hcompT⟩

  let wS : NormalControlWitnessV3 (Γ := Γ) hstepS :=
    { out := outS, comp := hcompS }

  let wT : BlockNormalControlWitnessV3 (Γ := Θ) hstepT :=
    { out := outT, comp := hcompT }

  let wCons :
      BlockNormalControlWitnessV3
        (Γ := Γ)
        (hstep := BigStepBlock.consNormal hstepS hstepT) :=
    BlockNormalControlWitnessV3.cons_normal wS wT h_eqS

  refine ⟨wCons.out, ?_⟩
  refine ⟨?_, wCons.comp⟩
  calc
    wCons.out.1 = wT.out.1 := by
      simp [wCons, BlockNormalControlWitnessV3.cons_normal_end_env]
    _ = outT.1 := rfl
    _ = Δ := h_eqT

/--
Bridge a normal block-body witness to a normal statement witness for `.block ss`.

This is the first point where block-body witnesses re-enter the statement-level
world.
-/
def block_stmt_normal_control_witness_v3
    {Γ : TypeEnv}
    {σ σ₀ σ₁ σ₂ : State}
    {ss : StmtBlock}
    {hopen : OpenScope σ σ₀}
    {hbody : BigStepBlock σ₀ ss .normal σ₁}
    {hclose : CloseScope σ₁ σ₂}
    (wBody : BlockNormalControlWitnessV3 (Γ := pushTypeScope Γ) hbody) :
    NormalControlWitnessV3
      (Γ := Γ)
      (st := .block ss)
      (hstep := BigStepStmt.block hopen hbody hclose) := by
  refine
    { out := ⟨Γ, HasTypeStmtCI.block wBody.out.2⟩
      comp := ?_ }
  -- hopen と hclose を明示的に供給する
  exact StmtControlCompatible.block (hopen := hopen) (hclose := hclose) wBody.comp

/--
Phase-1 block witness package:
- `nil`
- `consNormal`
- statement-level `.block` wrapper from a normal block-body witness
-/
structure StmtBlockNormalWitnessPhase1V3 : Type where
  nil_case :
    ∀ {Γ : TypeEnv} {σ : State},
      BlockNormalControlWitnessV3 (Γ := Γ) (hstep := BigStepBlock.nil (σ := σ))

  cons_normal_case :
    ∀ {Γ Θ : TypeEnv}
      {σ σ₁ σ₂ : State}
      {s : CppStmt} {ss : StmtBlock}
      {hstepS : BigStepStmt σ s .normal σ₁}
      {hstepT : BigStepBlock σ₁ ss .normal σ₂},
      (wS : NormalControlWitnessV3 (Γ := Γ) hstepS) →
      (wT : BlockNormalControlWitnessV3 (Γ := Θ) hstepT) →
      wS.out.1 = Θ →
      BlockNormalControlWitnessV3
        (Γ := Γ)
        (hstep := BigStepBlock.consNormal hstepS hstepT)

  block_stmt_case :
    ∀ {Γ : TypeEnv}
      {σ σ₀ σ₁ σ₂ : State}
      {ss : StmtBlock}
      {hopen : OpenScope σ σ₀}
      {hbody : BigStepBlock σ₀ ss .normal σ₁}
      {hclose : CloseScope σ₁ σ₂},
      BlockNormalControlWitnessV3 (Γ := pushTypeScope Γ) hbody →
      NormalControlWitnessV3
        (Γ := Γ)
        (st := .block ss)
        (hstep := BigStepStmt.block hopen hbody hclose)

/-- The phase-1 block package is already inhabited by the explicit constructors above. -/
def stmtBlockNormalWitnessPhase1V3_inst : StmtBlockNormalWitnessPhase1V3 := by
  refine
    { nil_case := ?_
      cons_normal_case := ?_
      block_stmt_case := ?_ }
  · intro Γ σ
    exact BlockNormalControlWitnessV3.nil (Γ := Γ) (σ := σ)
  · intro Γ Θ σ σ₁ σ₂ s ss hstepS hstepT wS wT hΘ
    exact BlockNormalControlWitnessV3.cons_normal wS wT hΘ
  · intro Γ σ σ₀ σ₁ σ₂ ss hopen hbody hclose wBody
    exact block_stmt_normal_control_witness_v3
      (Γ := Γ) (σ := σ) (σ₀ := σ₀) (σ₁ := σ₁) (σ₂ := σ₂)
      (ss := ss) (hopen := hopen) (hbody := hbody) (hclose := hclose)
      wBody

end Cpp
