import CppFormalization.Cpp2.Closure.Internal.ThinSeparatedDerefAssignKernel

namespace Cpp

/-!
Direct theorem surface for the fully theoremized strong thin-separated witness
family.

The previous file built the abstract kernel instance
`strongThinSeparatedWitnessKernel : SeparatedDerefAssignKernel`.
This file turns that instance back into concrete, easy-to-use theorems.

Why this matters:
- the separation-side story is now honest and directly consumable;
- downstream proofs no longer need to mention the abstract kernel explicitly;
- the remaining unsolved frontier is therefore *outside* this witness family.
-/


/- =========================================================
   1. Direct ready/readable replay theorems
   ========================================================= -/

theorem deref_place_ready_after_assign_of_strongThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    StrongThinSeparatedWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref e) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref e) τ := by
  intro w hσ' hready hstep
  exact deref_place_ready_after_assign_of_separated
    strongThinSeparatedWitnessKernel
    w hσ' hready hstep

theorem deref_load_readable_after_assign_of_strongThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    StrongThinSeparatedWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ) := by
  intro w hσ' hread hstep
  exact deref_load_readable_after_assign_of_separated
    strongThinSeparatedWitnessKernel
    w hσ' hread hstep


/- =========================================================
   2. Small constructors / coercions for downstream use
   ========================================================= -/

def StrongThinSeparatedWitness.ofAddrOf
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ →
    StrongThinSeparatedWitness Γ σ q rhs (.addrOf p) τ :=
  StrongThinSeparatedWitness.addrOf

def StrongThinSeparatedWitness.ofLoad
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    StrongThinSeparatedWitness Γ σ q rhs (.load p) τ :=
  StrongThinSeparatedWitness.load

@[simp] theorem StrongThinSeparatedWitness_toThin_addrOf
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType}
    (w : ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ) :
    (StrongThinSeparatedWitness.ofAddrOf w).toThin = w := by
  rfl

@[simp] theorem StrongThinSeparatedWitness_toThin_load
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType}
    (w : LoadThinSeparatedWitness Γ σ q rhs p τ) :
    (StrongThinSeparatedWitness.ofLoad w).toThin = w.base := by
  rfl


/- =========================================================
   3. Readable theorem for the two concrete source forms
   ========================================================= -/

theorem deref_place_ready_after_assign_of_addrOfThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref (.addrOf p)) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref (.addrOf p)) τ := by
  intro w hσ' hready hstep
  exact deref_place_ready_after_assign_of_strongThinSeparatedWitness
    (StrongThinSeparatedWitness.ofAddrOf w) hσ' hready hstep

theorem deref_place_ready_after_assign_of_loadThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref (.load p)) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref (.load p)) τ := by
  intro w hσ' hready hstep
  exact deref_place_ready_after_assign_of_strongThinSeparatedWitness
    (StrongThinSeparatedWitness.ofLoad w) hσ' hready hstep

theorem deref_load_readable_after_assign_of_addrOfThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref (.addrOf p)) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref (.addrOf p)) a' ∧ CellReadableTyped σ' a' τ) := by
  intro w hσ' hread hstep
  exact deref_load_readable_after_assign_of_strongThinSeparatedWitness
    (StrongThinSeparatedWitness.ofAddrOf w) hσ' hread hstep

theorem deref_load_readable_after_assign_of_loadThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref (.load p)) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref (.load p)) a' ∧ CellReadableTyped σ' a' τ) := by
  intro w hσ' hread hstep
  exact deref_load_readable_after_assign_of_strongThinSeparatedWitness
    (StrongThinSeparatedWitness.ofLoad w) hσ' hread hstep

end Cpp
