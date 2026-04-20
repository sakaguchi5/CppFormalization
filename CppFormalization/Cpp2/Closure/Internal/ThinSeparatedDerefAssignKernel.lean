import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.DerefAssignLocalInterfaces
import CppFormalization.Cpp2.Lemmas.ExprDeterminism

namespace Cpp

/-!
A thin concrete refinement of `SeparatedDerefAssignKernel`.

The goal is not to solve the deref/pointee frontier outright, but to make the
separation-side witness less opaque.

The witness is intentionally small:
- the pointer expression belongs to a source-stable fragment;
- the assignment has a concrete write target in the pre-state;
- that write target is separated from every address that the pointer expression
  may evaluate to.

What still remains axiomatic is exactly the semantic content we do not yet have:
- source-stable pointer-value preservation across the assignment;
- off-target preservation of live/readable cells.
-/


/- =========================================================
   1. A thin pointer-expression fragment
   ========================================================= -/

/--
Pointer expressions whose source-level replay is expected to be manageable by
the existing replay-stable infrastructure.

This keeps the fragment intentionally small:
- taking the address of a replay-stable read place;
- loading a pointer from a replay-stable read place.
-/
inductive ReplayStablePtrExpr : ValExpr → Prop where
  | addrOf {p : PlaceExpr} :
      ReplayStableReadPlace p →
      ReplayStablePtrExpr (.addrOf p)
  | load {p : PlaceExpr} :
      ReplayStableReadPlace p →
      ReplayStablePtrExpr (.load p)


/- =========================================================
   2. Thin concrete separation witness
   ========================================================= -/

/--
A thin concrete witness for separation-side deref transport.

`writeAddr` is the address written by the head assignment in the pre-state.
`ptrType` / `srcStable` describe the pointer expression side.
`targetSeparated` states that the assignment target is apart from any address
that the pointer expression can evaluate to.
-/
structure ThinSeparatedWitness
    (Γ : TypeEnv) (σ : State)
    (q : PlaceExpr) (rhs : ValExpr)
    (e : ValExpr) (τ : CppType) : Type where
  ptrType : HasValueType Γ e (.ptr τ)
  srcStable : ReplayStablePtrExpr e
  writeAddr : Nat
  writesQ : BigStepPlace σ q writeAddr
  targetSeparated :
    ∀ {a : Nat}, BigStepValue σ e (.addr a) → writeAddr ≠ a


/- =========================================================
   3. Thin concrete kernel on top of the witness
   ========================================================= -/

/--
Concrete separation-side kernel with an explicit witness shape.

What remains axiomatic is now sharper than before:
- preserve the pointer value for the thin source-stable fragment;
- preserve live/readable facts away from the written address.
-/
structure ThinSeparatedDerefAssignKernel : Type 1 where
  ptrValue_preserved :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      ThinSeparatedWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      PtrValueReadyAt Γ σ' e τ a

  cellLive_off_target_preserved :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      ThinSeparatedWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      CellLiveTyped σ' a τ

  cellReadable_off_target_preserved :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      ThinSeparatedWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      CellReadableTyped σ a τ →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      CellReadableTyped σ' a τ


/- =========================================================
   4. Small bridge lemmas
   ========================================================= -/

private theorem cellLiveTyped_of_cellReadableTyped
    {σ : State} {a : Nat} {τ : CppType} :
    CellReadableTyped σ a τ →
    CellLiveTyped σ a τ := by
  intro h
  rcases h with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
  exact ⟨c, hheap, hty, halive⟩

private theorem bigStepPlace_deref_of_ptrValueReadyAt_and_cellReadable
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {a : Nat} :
    PtrValueReadyAt Γ σ e τ a →
    CellReadableTyped σ a τ →
    BigStepPlace σ (.deref e) a := by
  intro hptr hread
  rcases hread with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
  exact BigStepPlace.deref (ptrValueReadyAt_bigStepValue hptr) hheap halive

private theorem cellReadableTyped_at_ptrAddr_of_derefReadable
    {Γ : TypeEnv} {σ : State}
    {e : ValExpr} {τ : CppType} {a : Nat}
    (hptr : PtrValueReadyAt Γ σ e τ a)
    (hread : ∃ b, BigStepPlace σ (.deref e) b ∧ CellReadableTyped σ b τ) :
    CellReadableTyped σ a τ := by
  rcases hread with ⟨b, hplace, hcell⟩
  cases hplace with
  | deref hval hheap halive =>
      have hEqVal :
          Value.addr a = Value.addr b := by
        exact bigStepValue_deterministic
          (ptrValueReadyAt_bigStepValue hptr) hval
      injection hEqVal with hab
      subst hab
      exact hcell


/- =========================================================
   5. Adapter back to the abstract local interface
   ========================================================= -/

/--
The thin concrete kernel yields an instance of the abstract local separation
interface by fixing `SepWitness` to `ThinSeparatedWitness`.
-/
def ThinSeparatedDerefAssignKernel.toSeparated
    (K : ThinSeparatedDerefAssignKernel) :
    SeparatedDerefAssignKernel where
  SepWitness := ThinSeparatedWitness

  ptrValueReadyAt_after_assign := by
    intro Γ σ σ' q rhs e τ a w hσ' hptr hlive hstep
    have hptr' : PtrValueReadyAt Γ σ' e τ a :=
      K.ptrValue_preserved w hσ' hptr hstep
    have hlive' : CellLiveTyped σ' a τ :=
      K.cellLive_off_target_preserved w hσ' hptr hlive hstep
    exact ⟨a, hptr', hlive'⟩

  derefLoadReadable_after_assign := by
    intro Γ σ σ' q rhs e τ w hσ' hread hstep
    rcases hread with ⟨a, hplace, hcell⟩
    cases hplace with
    | deref hval hheap halive =>
        let hptr : PtrValueReadyAt Γ σ e τ a := ⟨w.ptrType, hval⟩
        have hcell' : CellReadableTyped σ' a τ :=
          K.cellReadable_off_target_preserved w hσ' hptr hcell hstep
        have hplace' : BigStepPlace σ' (.deref e) a :=
          bigStepPlace_deref_of_ptrValueReadyAt_and_cellReadable
            (K.ptrValue_preserved w hσ' hptr hstep)
            hcell'
        exact ⟨a, hplace', hcell'⟩

end Cpp
