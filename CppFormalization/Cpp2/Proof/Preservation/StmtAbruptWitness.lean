import CppFormalization.Cpp2.Proof.Preservation.StmtNormalWitness

namespace Cpp

/-!
# Cpp2.Proof.Preservation.StmtAbruptWitness

Generic packaged witness layer for non-normal control flow.

Purpose:
- `StmtNormalWitness.lean` established the pattern for normal executions:
  execution-based witness package + compatibility package.
- For `while`, the unresolved bottleneck is the body-side `break` / `continue`
  typing supply.
- This file therefore introduces the *generic* packaged witness layer for an
  arbitrary control kind `k`, so that `break` and `continue` can be handled in
  exactly the same packaged style as normal witnesses.

This file is deliberately generic:
it does not pretend to prove abrupt witnesses yet.
It only provides the right bridge objects.
-/

/--
Execution-based witness package for an arbitrary control kind `k`.

`out` is the CI witness, and `comp` says that this witness is actually
compatible with the given execution.
-/
structure StmtControlWitnessV3
    (k : ControlKind)
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') : Type where
  out : {Δ : TypeEnv // HasTypeStmtCI k Γ st Δ}
  comp : StmtControlCompatible out.property hstep

namespace StmtControlWitnessV3

def end_env
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (w : StmtControlWitnessV3 k (Γ := Γ) hstep) :
    TypeEnv :=
  w.out.1

@[simp] theorem typing
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (w : StmtControlWitnessV3 k (Γ := Γ) hstep) :
    HasTypeStmtCI k Γ st w.out.1 :=
  w.out.2

/--
Transport a packaged control witness across a propositional equality of the
*start* environment.
-/
def transport_start_env
    {k : ControlKind}
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : StmtControlWitnessV3 k (Γ := Γ₁) hstep) :
    StmtControlWitnessV3 k (Γ := Γ₂) hstep := by
  subst hΓ
  exact w

@[simp] theorem transport_start_env_out
    {k : ControlKind}
    {Γ₁ Γ₂ : TypeEnv}
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (hΓ : Γ₁ = Γ₂)
    (w : StmtControlWitnessV3 k (Γ := Γ₁) hstep) :
    (transport_start_env hΓ w).out.1 = w.out.1 := by
  subst hΓ
  rfl

/--
Transport a packaged control witness across a propositional equality of the
*end* environment.
-/
def transport_end_env
    {k : ControlKind}
    {Γ : TypeEnv}
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    {Δ₁ Δ₂ : TypeEnv}
    (hΔ : Δ₁ = Δ₂)
    (w : StmtControlWitnessV3 k (Γ := Γ) hstep)
    (hout : w.out.1 = Δ₁) :
    StmtControlWitnessV3 k (Γ := Γ) hstep := by
  refine
    { out := ⟨Δ₂, HasTypeStmtCI.transport_end_env (hout.trans hΔ) w.out.2⟩
      comp := ?_ }
  exact StmtControlCompatible.transport_end_env (hout.trans hΔ) w.comp

@[simp] theorem transport_end_env_out
    {k : ControlKind}
    {Γ : TypeEnv}
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    {Δ₁ Δ₂ : TypeEnv}
    (hΔ : Δ₁ = Δ₂)
    (w : StmtControlWitnessV3 k (Γ := Γ) hstep)
    (hout : w.out.1 = Δ₁) :
    (transport_end_env hΔ w hout).out.1 = Δ₂ := by
  rfl

/-- Convert back to the existential-with-compatibility shape. -/
theorem to_exists
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    (w : StmtControlWitnessV3 k (Γ := Γ) hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI k Γ st Δ},
      StmtControlCompatible out.property hstep := by
  exact ⟨w.out, w.comp⟩

/-- Build the packaged form from the existential-with-compatibility shape. -/
def of_exists
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'}
    -- ∃ ではなく Subtype ({ // }) を使用して情報を維持する
    (h : { out : {Δ : TypeEnv // HasTypeStmtCI k Γ st Δ} //
           StmtControlCompatible out.property hstep }) :
    StmtControlWitnessV3 k (Γ := Γ) hstep := by
  rcases h with ⟨out, hcomp⟩
  exact { out := out, comp := hcomp }

end StmtControlWitnessV3

/--
A packaged control witness together with a chosen end environment `Δ`.

This is the abrupt analogue of `NormalControlWitnessAtV3`.
-/
structure StmtControlWitnessAtV3
    (k : ControlKind)
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') (Δ : TypeEnv) : Type where
  witness : StmtControlWitnessV3 k (Γ := Γ) hstep
  end_eq : witness.out.1 = Δ

namespace StmtControlWitnessAtV3

@[simp] theorem end_env
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'} {Δ : TypeEnv}
    (w : StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ) :
    w.witness.out.1 = Δ :=
  w.end_eq

@[simp] def forget
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'} {Δ : TypeEnv}
    (w : StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ) :
    StmtControlWitnessV3 k (Γ := Γ) hstep :=
  w.witness

@[simp] theorem typing
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'} {Δ : TypeEnv}
    (w : StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ) :
    HasTypeStmtCI k Γ st Δ := by
  exact HasTypeStmtCI.transport_end_env w.end_eq w.witness.out.2

theorem to_exists
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'} {Δ : TypeEnv}
    (w : StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ) :
    ∃ out : {Ξ : TypeEnv // HasTypeStmtCI k Γ st Ξ},
      out.1 = Δ ∧
      StmtControlCompatible out.property hstep := by
  exact ⟨w.witness.out, w.end_eq, w.witness.comp⟩

def of_exists
    {k : ControlKind}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    {hstep : BigStepStmt σ st ctrl σ'} {Δ : TypeEnv}
    -- ∃ を Subtype に変更して、Prop ではなく Type 宇宙のデータとして受け取る
    (h : { out : {Ξ : TypeEnv // HasTypeStmtCI k Γ st Ξ} //
           out.1 = Δ ∧ StmtControlCompatible out.property hstep }) :
    StmtControlWitnessAtV3 k (Γ := Γ) hstep Δ := by
  rcases h with ⟨out, h_eq, hcomp⟩
  exact
    { witness := { out := out, comp := hcomp }
      end_eq := h_eq }

end StmtControlWitnessAtV3

abbrev BreakControlWitnessV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') :=
  StmtControlWitnessV3 .breakK (Γ := Γ) hstep

abbrev ContinueControlWitnessV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') :=
  StmtControlWitnessV3 .continueK (Γ := Γ) hstep

abbrev BreakControlWitnessAtV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') (Δ : TypeEnv) :=
  StmtControlWitnessAtV3 .breakK (Γ := Γ) hstep Δ

abbrev ContinueControlWitnessAtV3
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
    (hstep : BigStepStmt σ st ctrl σ') (Δ : TypeEnv) :=
  StmtControlWitnessAtV3 .continueK (Γ := Γ) hstep Δ

end Cpp
