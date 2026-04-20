import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.DerefAssignLocalInterfaces
import CppFormalization.Cpp2.Lemmas.ExprDeterminism
import CppFormalization.Cpp2.Lemmas.AssignWriteFootprint

namespace Cpp


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

Important limitation:
for `e = .load p`, `targetSeparated` only separates the head write target from
the *loaded pointer value* address, not from the address of the source pointer
cell itself. So this witness is already strong enough to theoremize the
`addrOf` case and off-target heap preservation, but not yet strong enough to
eliminate the remaining `load` case.
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

What remains axiomatic at this layer:
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
   4. Small bridge lemmas used by the abstract adapter
   ========================================================= -/

private theorem bigStepPlace_deref_of_ptrValueReadyAt_and_cellReadable
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {a : Nat} :
    PtrValueReadyAt Γ σ e τ a →
    CellReadableTyped σ a τ →
    BigStepPlace σ (.deref e) a := by
  intro hptr hread
  rcases hread with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
  exact BigStepPlace.deref (ptrValueReadyAt_bigStepValue hptr) hheap halive

private theorem thinSeparatedWitness_writeAddr_ne_of_ptrValueReadyAt
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat}
    (w : ThinSeparatedWitness Γ σ q rhs e τ)
    (hptr : PtrValueReadyAt Γ σ e τ a) :
    w.writeAddr ≠ a := by
  exact w.targetSeparated (ptrValueReadyAt_bigStepValue hptr)

private theorem thinSeparatedWitness_heapCell_preserved_off_target
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat} {c : Cell}
    (w : ThinSeparatedWitness Γ σ q rhs e τ)
    (hptr : PtrValueReadyAt Γ σ e τ a)
    (hheap : σ.heap a = some c)
    (hstep : BigStepStmt σ (.assign q rhs) .normal σ') :
    σ'.heap a = some c := by
  have hneqW : w.writeAddr ≠ a :=
    thinSeparatedWitness_writeAddr_ne_of_ptrValueReadyAt w hptr
  have hneq : a ≠ w.writeAddr := by
    intro ha
    apply hneqW
    simp [ha]
  exact bigStepStmt_assign_heap_unchanged_off_target
    w.writesQ hneq hheap hstep

private theorem ptrValue_addrOf_preserved_of_thinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} {a : Nat}
    (w : ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ)
    (hptr : PtrValueReadyAt Γ σ (.addrOf p) τ a)
    (hstep : BigStepStmt σ (.assign q rhs) .normal σ') :
    PtrValueReadyAt Γ σ' (.addrOf p) τ a := by
  have hpstable : ReplayStableReadPlace p := by
    cases w.srcStable with
    | addrOf hp =>
        exact hp
  rcases hptr with ⟨hty, hval⟩
  cases hval with
  | addrOf hplace =>
      have hplace' : BigStepPlace σ' p a :=
        bigStepPlace_replayStableReadPlace_after_assign hpstable hplace hstep
      exact ⟨w.ptrType, BigStepValue.addrOf hplace'⟩


/- =========================================================
   5. Refined kernel: split the true remaining frontier
   ========================================================= -/

/--
A refined separation-side kernel.

Compared to `ThinSeparatedDerefAssignKernel`, this version no longer treats
off-target heap preservation or the `addrOf` case as axiomatic. Those are now
theorems from the concrete witness plus the assignment semantics.

What really remains open is the `load` case:
to preserve `PtrValueReadyAt Γ σ (.load p) τ a`, one needs a stronger source-cell
separation fact than the current `ThinSeparatedWitness` provides.
-/
structure ThinSeparatedDerefAssignKernelRefined : Type 1 where
  /--
  `load`-based pointer expressions survive the assignment.

  This is the genuinely heavier case, because it depends on preserving the
  pointer cell's stored address value. The current witness does not yet expose
  enough source-cell separation to make this a theorem.
  -/
  ptrValue_load_preserved :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {p : PlaceExpr} {τ : CppType} {a : Nat},
      ThinSeparatedWitness Γ σ q rhs (.load p) τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ (.load p) τ a →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      PtrValueReadyAt Γ σ' (.load p) τ a


/- =========================================================
   6. Derived theorems from the refined kernel
   ========================================================= -/

theorem ptrValue_preserved_of_refined
    (K : ThinSeparatedDerefAssignKernelRefined)
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat} :
    ThinSeparatedWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PtrValueReadyAt Γ σ e τ a →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PtrValueReadyAt Γ σ' e τ a := by
  intro w hσ' hptr hstep
  cases hsrc : w.srcStable with
  | addrOf hp =>
      simpa [hsrc] using
        ptrValue_addrOf_preserved_of_thinSeparatedWitness w hptr hstep
  | load hp =>
      simpa [hsrc] using
        K.ptrValue_load_preserved w hσ' hptr hstep

theorem cellLive_off_target_preserved_of_refined
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat} :
    ThinSeparatedWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PtrValueReadyAt Γ σ e τ a →
    CellLiveTyped σ a τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    CellLiveTyped σ' a τ := by
  intro w hσ' hptr hlive hstep
  rcases hlive with ⟨c, hheap, hty, halive⟩
  have hheap' : σ'.heap a = some c :=
    thinSeparatedWitness_heapCell_preserved_off_target w hptr hheap hstep
  exact ⟨c, hheap', hty, halive⟩

theorem cellReadable_off_target_preserved_of_refined
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat} :
    ThinSeparatedWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PtrValueReadyAt Γ σ e τ a →
    CellReadableTyped σ a τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    CellReadableTyped σ' a τ := by
  intro w hσ' hptr hread hstep
  rcases hread with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
  have hheap' : σ'.heap a = some c :=
    thinSeparatedWitness_heapCell_preserved_off_target w hptr hheap hstep
  exact ⟨c, v, hheap', hty, halive, hval, hcompat⟩


/- =========================================================
   7. Adapters
   ========================================================= -/

/--
A refined kernel automatically yields the earlier thin separation-side kernel.
-/
def ThinSeparatedDerefAssignKernelRefined.toThinSeparated
    (K : ThinSeparatedDerefAssignKernelRefined) :
    ThinSeparatedDerefAssignKernel where
  ptrValue_preserved := by
    intro Γ σ σ' q rhs e τ a w hσ' hptr hstep
    exact ptrValue_preserved_of_refined K w hσ' hptr hstep

  cellLive_off_target_preserved := by
    intro Γ σ σ' q rhs e τ a w hσ' hptr hlive hstep
    exact cellLive_off_target_preserved_of_refined w hσ' hptr hlive hstep

  cellReadable_off_target_preserved := by
    intro Γ σ σ' q rhs e τ a w hσ' hptr hread hstep
    exact cellReadable_off_target_preserved_of_refined w hσ' hptr hread hstep

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

/--
Direct adapter from the refined kernel all the way back to the abstract local
interface.
-/
def ThinSeparatedDerefAssignKernelRefined.toSeparated
    (K : ThinSeparatedDerefAssignKernelRefined) :
    SeparatedDerefAssignKernel :=
  K.toThinSeparated.toSeparated

end Cpp
