import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.PtrExprAssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.DerefAssignTransportKernel

namespace Cpp

/-!
Local proof interfaces for the remaining deref/pointee frontier.

These interfaces are designed to sit *on top of* the latest split:

- `PtrExprAssignTransportKernel` handles expression-level pointer replay.
- `DerefAssignTransportKernel` isolates the stronger pointee-live/readable gap.

The goal here is not to solve that gap yet, but to expose two honest ways of
solving it later without pretending that one global unconditional axiom is
mathematically natural.

A. Separation-style local reasoning:
   the assignment is accompanied by a witness that its write footprint is
   separated from the dereference dependency of `e`.

B. Protocol/Ghost-style local reasoning:
   the dereference dependency of `e` is protected by some protocol token, and
   the assignment comes with an update witness showing it respects that protocol.
-/


/- =========================================================
   A. Separation-style local interface
   ========================================================= -/

/--
A local separation-style interface for deref/pointee transport.

`SepWitness Γ σ q rhs e τ` should be read as:
the assignment `q := rhs` is locally separated from the dereference dependency
of the pointer expression `e : ptr τ` in the pre-state `σ`.

This interface does **not** specify what that witness is.
It only records the theorem shape that a future implementation must provide.
-/

/-
「現段階では witness family を Type-valued に固定し、kernel 自身は Type 1 とする。
universe polymorphism は必要になった時点で導入する」
-/
structure SeparatedDerefAssignKernel : Type 1 where
  SepWitness :
    TypeEnv → State → PlaceExpr → ValExpr → ValExpr → CppType → Type

  ptrValueReadyAt_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      SepWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', PtrValueReadyAt Γ σ' e τ a' ∧ CellLiveTyped σ' a' τ

  derefLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType},
      SepWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ

theorem deref_place_ready_after_assign_of_separated
    (K : SeparatedDerefAssignKernel)
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    K.SepWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref e) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref e) τ := by
  intro hsep hσ' hready hstep
  cases hready with
  | deref hptr hlive =>
      rcases K.ptrValueReadyAt_after_assign hsep hσ' hptr hlive hstep with
        ⟨a', hptr', hlive'⟩
      exact PlaceReadyConcrete.deref hptr' hlive'

theorem deref_load_readable_after_assign_of_separated
    (K : SeparatedDerefAssignKernel)
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    K.SepWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ) := by
  intro hsep hσ' hread hstep
  exact K.derefLoadReadable_after_assign hsep hσ' hread hstep


/- =========================================================
   B. Protocol / ghost-style local interface
   ========================================================= -/

/--
A local protocol-style interface for deref/pointee transport.

`Token Γ σ e τ` is a ghost/protocol witness protecting the dereference
dependency of `e : ptr τ` in state `σ`.
`UpdateWitness Γ σ q rhs e τ` is a witness that the assignment `q := rhs`
respects the protocol governing that dependency.

Again, this interface intentionally does not fix one concrete ghost design.
It only isolates the theorem obligations.
-/
structure ProtocolDerefAssignKernel : Type 1 where
  Token :
    TypeEnv → State → ValExpr → CppType → Type

  UpdateWitness :
    TypeEnv → State → PlaceExpr → ValExpr → ValExpr → CppType → Type

  ptrValueReadyAt_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      Token Γ σ e τ →
      UpdateWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', PtrValueReadyAt Γ σ' e τ a' ∧ CellLiveTyped σ' a' τ

  derefLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType},
      Token Γ σ e τ →
      UpdateWitness Γ σ q rhs e τ →
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ

theorem deref_place_ready_after_assign_of_protocol
    (K : ProtocolDerefAssignKernel)
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    K.Token Γ σ e τ →
    K.UpdateWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref e) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref e) τ := by
  intro htok hupd hσ' hready hstep
  cases hready with
  | deref hptr hlive =>
      rcases K.ptrValueReadyAt_after_assign htok hupd hσ' hptr hlive hstep with
        ⟨a', hptr', hlive'⟩
      exact PlaceReadyConcrete.deref hptr' hlive'

theorem deref_load_readable_after_assign_of_protocol
    (K : ProtocolDerefAssignKernel)
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    K.Token Γ σ e τ →
    K.UpdateWitness Γ σ q rhs e τ →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ) := by
  intro htok hupd hσ' hread hstep
  exact K.derefLoadReadable_after_assign htok hupd hσ' hread hstep

end Cpp
