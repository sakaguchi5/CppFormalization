import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlPreservation

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtNormalWitness

Execution-based witness workbench for normal completion.

This file stays deliberately honest:
- it does **not** claim the global theorem
  `normal_control_witness_of_bigStep_v3`;
- it records the cases that are already theorem-backed:
  `skip`, `assign`, `seqNormal`, and `if` true/false normal;
- it packages the transport-heavy witness bookkeeping so later files can build on
  it without reopening the same dependent-transport ceremony every time.
-/

/--
Execution-based normal witness package.

`out` is the CI normal witness, and `comp` says that this witness is actually
compatible with the given normal execution.
-/
structure NormalControlWitnessV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') : Type where
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

This is the abstraction that hides the start-environment transport noise.
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
      simp [wSeq, NormalControlWitnessV3.seq_normal_end_env]
    _ = outT.1 := rfl
    _ = Δ := h_eqT

/--
Phase-1 normal witness package:
- `skip`
- `assign`
- `seqNormal`
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

/--
`exprStmt` is another atomic normal case:
the CI witness and the compatibility witness are both already constructor-shaped.
-/
def exprStmt_normal_control_witness_v3
    {Γ : TypeEnv} {σ : State}
    {e : ValExpr} {τ : CppType}
    (hv : HasValueType Γ e τ)
    {hstep : BigStepStmt σ (.exprStmt e) .normal σ} :
    NormalControlWitnessV3 (Γ := Γ) hstep := by
  refine
    { out := ⟨Γ, HasTypeStmtCI.exprStmt hv⟩
      comp := ?_ }
  simpa using
    (StmtControlCompatible.exprStmt
      (Γ := Γ) (σ := σ) (hv := hv) (hstep := hstep))

/--
Object declaration without initializer.
-/
def declareObjNone_normal_control_witness_v3
    {Γ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident}
    (hfresh : currentTypeScopeFresh Γ x)
    (hobj : ObjectType τ)
    {hstep : BigStepStmt σ (.declareObj τ x none) .normal σ'} :
    NormalControlWitnessV3 (Γ := Γ) hstep := by
  refine
    { out := ⟨declareTypeObject Γ x τ, HasTypeStmtCI.declareObjNone hfresh hobj⟩
      comp := ?_ }
  simpa using
    (StmtControlCompatible.declareObjNone
      (Γ := Γ) (σ := σ) (σ' := σ')
      (hfresh := hfresh) (hobj := hobj) (hstep := hstep))

/--
Object declaration with initializer.
-/
def declareObjSome_normal_control_witness_v3
    {Γ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {e : ValExpr}
    (hfresh : currentTypeScopeFresh Γ x)
    (hobj : ObjectType τ)
    (hv : HasValueType Γ e τ)
    {hstep : BigStepStmt σ (.declareObj τ x (some e)) .normal σ'} :
    NormalControlWitnessV3 (Γ := Γ) hstep := by
  refine
    { out := ⟨declareTypeObject Γ x τ, HasTypeStmtCI.declareObjSome hfresh hobj hv⟩
      comp := ?_ }
  simpa using
    (StmtControlCompatible.declareObjSome
      (Γ := Γ) (σ := σ) (σ' := σ')
      (hfresh := hfresh) (hobj := hobj) (hv := hv) (hstep := hstep))

/--
Reference declaration.
-/
def declareRef_normal_control_witness_v3
    {Γ : TypeEnv} {σ σ' : State}
    {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hfresh : currentTypeScopeFresh Γ x)
    (hp : HasPlaceType Γ p τ)
    {hstep : BigStepStmt σ (.declareRef τ x p) .normal σ'} :
    NormalControlWitnessV3 (Γ := Γ) hstep := by
  refine
    { out := ⟨declareTypeRef Γ x τ, HasTypeStmtCI.declareRef hfresh hp⟩
      comp := ?_ }
  simpa using
    (StmtControlCompatible.declareRef
      (Γ := Γ) (σ := σ) (σ' := σ')
      (hfresh := hfresh) (hp := hp) (hstep := hstep))

/--
Phase-2 package:
phase-1 plus the remaining atomic/declaration normal cases.
-/
structure StmtNormalWitnessPhase2V3 : Type extends StmtNormalWitnessPhase1V3  where
  exprStmt_case :
    ∀ {Γ : TypeEnv} {σ : State}
      {e : ValExpr} {τ : CppType},
      HasValueType Γ e τ →
      ∀ {hstep : BigStepStmt σ (.exprStmt e) .normal σ},
        NormalControlWitnessV3 (Γ := Γ) hstep

  declareObjNone_case :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x : Ident},
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      ∀ {hstep : BigStepStmt σ (.declareObj τ x none) .normal σ'},
        NormalControlWitnessV3 (Γ := Γ) hstep

  declareObjSome_case :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x : Ident} {e : ValExpr},
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasValueType Γ e τ →
      ∀ {hstep : BigStepStmt σ (.declareObj τ x (some e)) .normal σ'},
        NormalControlWitnessV3 (Γ := Γ) hstep

  declareRef_case :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {τ : CppType} {x : Ident} {p : PlaceExpr},
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      ∀ {hstep : BigStepStmt σ (.declareRef τ x p) .normal σ'},
        NormalControlWitnessV3 (Γ := Γ) hstep

/--
Phase-2 is already inhabited by the explicit atomic/declaration witness builders.
-/
def stmtNormalWitnessPhase2V3_inst : StmtNormalWitnessPhase2V3 := by
  refine
    { toStmtNormalWitnessPhase1V3 := stmtNormalWitnessPhase1V3_inst
      exprStmt_case := ?_
      declareObjNone_case := ?_
      declareObjSome_case := ?_
      declareRef_case := ?_ }
  · intro Γ σ e τ hv hstep
    exact exprStmt_normal_control_witness_v3 (Γ := Γ) (σ := σ) hv (hstep := hstep)
  · intro Γ σ σ' τ x hfresh hobj hstep
    exact declareObjNone_normal_control_witness_v3
      (Γ := Γ) (σ := σ) (σ' := σ') hfresh hobj (hstep := hstep)
  · intro Γ σ σ' τ x e hfresh hobj hv hstep
    exact declareObjSome_normal_control_witness_v3
      (Γ := Γ) (σ := σ) (σ' := σ') hfresh hobj hv (hstep := hstep)
  · intro Γ σ σ' τ x p hfresh hp hstep
    exact declareRef_normal_control_witness_v3
      (Γ := Γ) (σ := σ) (σ' := σ') hfresh hp (hstep := hstep)

@[simp] theorem HasTypeStmtCI.transport_end_env
    {k : ControlKind} {Γ Δ₁ Δ₂ : TypeEnv} {st : CppStmt}
    (hΔ : Δ₁ = Δ₂)
    (hty : HasTypeStmtCI k Γ st Δ₁) :
    HasTypeStmtCI k Γ st Δ₂ := by
  subst hΔ
  exact hty

@[simp] theorem HasTypeStmtCI.transport_end_env_symm
    {k : ControlKind} {Γ Δ₁ Δ₂ : TypeEnv} {st : CppStmt}
    (hΔ : Δ₂ = Δ₁)
    (hty : HasTypeStmtCI k Γ st Δ₁) :
    HasTypeStmtCI k Γ st Δ₂ := by
  subst hΔ
  exact hty

@[simp] theorem StmtControlCompatible.transport_end_env
    {k : ControlKind} {Γ Δ₁ Δ₂ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    {hty : HasTypeStmtCI k Γ st Δ₁}
    (hΔ : Δ₁ = Δ₂)
    (hcomp : StmtControlCompatible hty hstep) :
    StmtControlCompatible (HasTypeStmtCI.transport_end_env hΔ hty) hstep := by
  subst hΔ
  exact hcomp

/--
A normal witness package together with a chosen target end environment `Δ`.

This is the right bridge object for branch-merging proofs:
it says not only that we have an execution-based witness package,
but also that its end environment has already been identified with `Δ`.
-/
structure NormalControlWitnessAtV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    (hstep : BigStepStmt σ st .normal σ') (Δ : TypeEnv) : Type where
  witness : NormalControlWitnessV3 (Γ := Γ) hstep
  end_eq : witness.out.1 = Δ

namespace NormalControlWitnessAtV3

@[simp] theorem end_env
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'} {Δ : TypeEnv}
    (w : NormalControlWitnessAtV3 (Γ := Γ) hstep Δ) :
    w.witness.out.1 = Δ :=
  w.end_eq

@[simp] def forget
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'} {Δ : TypeEnv}
    (w : NormalControlWitnessAtV3 (Γ := Γ) hstep Δ) :
    NormalControlWitnessV3 (Γ := Γ) hstep :=
  w.witness

theorem to_exists
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'} {Δ : TypeEnv}
    (w : NormalControlWitnessAtV3 (Γ := Γ) hstep Δ) :
    ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ st Ξ},
      out.1 = Δ ∧
      StmtControlCompatible out.property hstep := by
  exact ⟨w.witness.out, w.end_eq, w.witness.comp⟩

def of_exists
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'} {Δ : TypeEnv}
    -- ∃ の代わりに { ... // ... } (Subtype) または Σ を使う
    (h : { out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ st Ξ} //
           out.1 = Δ ∧ StmtControlCompatible out.property hstep }) :
    NormalControlWitnessAtV3 (Γ := Γ) hstep Δ := by
  rcases h with ⟨out, h_eq, hcomp⟩
  exact
    { witness := { out := out, comp := hcomp }
      end_eq := h_eq }

end NormalControlWitnessAtV3

/--
Packaged branch input for the `if`-true normal case.
-/
structure IteTrueNormalBranchInputV3
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    {hcond : BigStepValue σ c (.bool true)}
    {hstepS : BigStepStmt σ s .normal σ'} : Type where
  true_branch : NormalControlWitnessAtV3 (Γ := Γ) hstepS Δ
  false_branch : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ t Δ'}
  false_end_eq : false_branch.1 = Δ

/--
Packaged branch input for the `if`-false normal case.
-/
structure IteFalseNormalBranchInputV3
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    {hstepT : BigStepStmt σ t .normal σ'} : Type where
  true_branch : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ s Δ'}
  true_end_eq : true_branch.1 = Δ
  false_branch : NormalControlWitnessAtV3 (Γ := Γ) hstepT Δ

namespace NormalControlWitnessAtV3

/--
Merge packaged inputs for the `if`-true normal case into a packaged normal witness
at the common end environment `Δ`.
-/
def ite_true_normal
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    {hcond : BigStepValue σ c (.bool true)}
    {hstepS : BigStepStmt σ s .normal σ'}
    (hc : HasValueType Γ c (.base .bool))
    (hin : IteTrueNormalBranchInputV3
      (Γ := Γ) (Δ := Δ)
      (c := c) (s := s) (t := t)
      (hcond := hcond) (hstepS := hstepS)) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (st := .ite c s t)
      (hstep := BigStepStmt.iteTrue hcond hstepS)
      Δ := by
  let htyT' : HasTypeStmtCI .normalK Γ t hin.true_branch.witness.out.1 :=
    HasTypeStmtCI.transport_end_env
      (hin.false_end_eq.trans hin.true_branch.end_eq.symm)
      hin.false_branch.2
  refine
    { witness :=
        { out := ⟨hin.true_branch.witness.out.1, HasTypeStmtCI.ite hc hin.true_branch.witness.out.2 htyT'⟩
          comp := ?_ }
      end_eq := hin.true_branch.end_eq }
  exact StmtControlCompatible.ite_true
    (hcond := hcond) (hc := hc) (htyT := htyT') hin.true_branch.witness.comp

/--
Merge packaged inputs for the `if`-false normal case into a packaged normal witness
at the common end environment `Δ`.
-/
def ite_false_normal
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    {hcond : BigStepValue σ c (.bool false)}
    {hstepT : BigStepStmt σ t .normal σ'}
    (hc : HasValueType Γ c (.base .bool))
    (hin : IteFalseNormalBranchInputV3
      (Γ := Γ) (Δ := Δ)
      (c := c) (s := s) (t := t)
      (hcond := hcond) (hstepT := hstepT)) :
    NormalControlWitnessAtV3
      (Γ := Γ)
      (st := .ite c s t)
      (hstep := BigStepStmt.iteFalse hcond hstepT)
      Δ := by
  let htyS' : HasTypeStmtCI .normalK Γ s hin.false_branch.witness.out.1 :=
    HasTypeStmtCI.transport_end_env
      (hin.true_end_eq.trans hin.false_branch.end_eq.symm)
      hin.true_branch.2
  refine
    { witness :=
        { out := ⟨hin.false_branch.witness.out.1, HasTypeStmtCI.ite hc htyS' hin.false_branch.witness.out.2⟩
          comp := ?_ }
      end_eq := hin.false_branch.end_eq }
  exact StmtControlCompatible.ite_false
    (hcond := hcond) (hc := hc) (htyS := htyS') hin.false_branch.witness.comp

end NormalControlWitnessAtV3

/--
Normal witness for the `if`-true branch, using packaged branch inputs.
-/
def ite_true_normal_control_witness_v3
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    {hcond : BigStepValue σ c (.bool true)}
    {hstepS : BigStepStmt σ s .normal σ'}
    (houtS :
      ∃ outS : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ s Δ'},
        outS.1 = Δ ∧ StmtControlCompatible outS.property hstepS)
    (houtT :
      ∃ outT : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ t Δ'},
        outT.1 = Δ) :
    ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Ξ},
      out.1 = Δ ∧
      StmtControlCompatible out.property (BigStepStmt.iteTrue hcond hstepS) := by
  -- 1. まず houtS を分解して具体的な実体 (outS, h_eqS, hcompS) を取り出す
  rcases houtS with ⟨outS, h_eqS, hcompS⟩
  -- 2. houtT も同様に分解（Classical を使う必要はありません）
  rcases houtT with ⟨outT, h_eqT⟩

  -- 3. 分解したパーツから直接 hin を組み立てる
  let hin : IteTrueNormalBranchInputV3
      (Γ := Γ) (Δ := Δ)
      (c := c) (s := s) (t := t)
      (hcond := hcond) (hstepS := hstepS) :=
    { true_branch := { witness := { out := outS, comp := hcompS }, end_eq := h_eqS }
      false_branch := outT
      false_end_eq := h_eqT }

  -- 4. パッケージ化された関数を呼び出し、to_exists で ∃ に戻す
  exact (NormalControlWitnessAtV3.ite_true_normal (hcond := hcond) (hstepS := hstepS) hc hin).to_exists

/--
Normal witness for the `if`-false branch, using packaged branch inputs.
-/
def ite_false_normal_control_witness_v3
    {Γ Δ : TypeEnv}
    {σ σ' : State}
    {c : ValExpr} {s t : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    {hcond : BigStepValue σ c (.bool false)}
    {hstepT : BigStepStmt σ t .normal σ'}
    (houtS :
      ∃ outS : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ s Δ'},
        outS.1 = Δ)
    (houtT :
      ∃ outT : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ t Δ'},
        outT.1 = Δ ∧ StmtControlCompatible outT.property hstepT) :
    ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Ξ},
      out.1 = Δ ∧
      StmtControlCompatible out.property (BigStepStmt.iteFalse hcond hstepT) := by
  -- 1. Prop 宇宙の存在量化を分解して中身を取り出す
  rcases houtS with ⟨outS, h_eqS⟩
  rcases houtT with ⟨outT, h_eqT, hcompT⟩

  -- 2. 取り出したパーツで直接 IteFalseNormalBranchInputV3 を構成
  let hin : IteFalseNormalBranchInputV3
      (Γ := Γ) (Δ := Δ)
      (c := c) (s := s) (t := t)
      (hcond := hcond) (hstepT := hstepT) :=
    { true_branch := outS
      true_end_eq := h_eqS
      false_branch := { witness := { out := outT, comp := hcompT }, end_eq := h_eqT } }

  -- 3. 合成関数を呼び出し、結果を ∃ に戻す
  exact (NormalControlWitnessAtV3.ite_false_normal (hcond := hcond) (hstepT := hstepT) hc hin).to_exists

/--
Phase-3 package:
phase-2 plus `if` true/false normal cases.
-/
structure StmtNormalWitnessPhase3V3 : Type extends StmtNormalWitnessPhase2V3  where
  ite_true_case :
    ∀ {Γ Δ : TypeEnv}
      {σ σ' : State}
      {c : ValExpr} {s t : CppStmt},
      HasValueType Γ c (.base .bool) →
      ∀ {hcond : BigStepValue σ c (.bool true)}
        {hstepS : BigStepStmt σ s .normal σ'},
      (∃ outS : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ s Δ'},
        outS.1 = Δ ∧ StmtControlCompatible outS.property hstepS) →
      (∃ outT : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ t Δ'},
        outT.1 = Δ) →
      ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Ξ},
        out.1 = Δ ∧
        StmtControlCompatible out.property (BigStepStmt.iteTrue hcond hstepS)

  ite_false_case :
    ∀ {Γ Δ : TypeEnv}
      {σ σ' : State}
      {c : ValExpr} {s t : CppStmt},
      HasValueType Γ c (.base .bool) →
      ∀ {hcond : BigStepValue σ c (.bool false)}
        {hstepT : BigStepStmt σ t .normal σ'},
      (∃ outS : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ s Δ'},
        outS.1 = Δ) →
      (∃ outT : {Δ' : TypeEnv // HasTypeStmtCI .normalK Γ t Δ'},
        outT.1 = Δ ∧ StmtControlCompatible outT.property hstepT) →
      ∃ out : {Ξ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Ξ},
        out.1 = Δ ∧
        StmtControlCompatible out.property (BigStepStmt.iteFalse hcond hstepT)

/-- Phase-3 is already inhabited by phase-2 plus the explicit `if` constructors above. -/
def stmtNormalWitnessPhase3V3_inst : StmtNormalWitnessPhase3V3 := by
  refine
    { toStmtNormalWitnessPhase2V3 := stmtNormalWitnessPhase2V3_inst
      ite_true_case := ?_
      ite_false_case := ?_ }
  · intro Γ Δ σ σ' c s t hc hcond hstepS houtS houtT
    exact ite_true_normal_control_witness_v3
      (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (c := c) (s := s) (t := t) hc
      (hcond := hcond) (hstepS := hstepS) houtS houtT
  · intro Γ Δ σ σ' c s t hc hcond hstepT houtS houtT
    exact ite_false_normal_control_witness_v3
      (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ')
      (c := c) (s := s) (t := t) hc
      (hcond := hcond) (hstepT := hstepT) houtS houtT

end Cpp
