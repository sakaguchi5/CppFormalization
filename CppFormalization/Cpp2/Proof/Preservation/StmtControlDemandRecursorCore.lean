import CppFormalization.Cpp2.Proof.Preservation.Demand.FromReady
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Static.Safety.StateInvariantConcrete
namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandRecursorCore

A demand-oriented replacement target for the old readiness-transport recursor.

This file intentionally does not introduce an axiom.  It fixes the theorem target
that should replace `readinessTransportNormalCore`:

* preservation consumes path-sensitive execution demand;
* `seq` and block `cons` use the post-state demand carried by the demand
  evidence, not an unrestricted readiness transport lemma.
-/

/-- Statement preservation goal from demand. -/
abbrev StmtDemandPreservationGoal
    (Γ Δ : TypeEnv) (st : CppStmt)
    (σ : State) (ctrl : CtrlResult) (σ' : State) : Prop :=
  StmtExecutionDemand Γ σ st ctrl σ' Δ →
  ScopedTypedStateConcrete Γ σ →
  ScopedTypedStateConcrete Δ σ'

/-- Block preservation goal from demand. -/
abbrev BlockDemandPreservationGoal
    (Γ Δ : TypeEnv) (ss : StmtBlock)
    (σ : State) (ctrl : CtrlResult) (σ' : State) : Prop :=
  BlockExecutionDemand Γ σ ss ctrl σ' Δ →
  ScopedTypedStateConcrete Γ σ →
  ScopedTypedStateConcrete Δ σ'

/--
Kernel shape expected from the future demand recursor.

This is the demand-side analogue of `StmtBlockPreservationKernel`, but it no
longer accepts `StmtReadyConcrete` / `BlockReadyConcrete` as entry arguments.
The entry and tail readiness facts live inside `StmtExecutionDemand` /
`BlockExecutionDemand` at the exact program points where they are consumed.
-/
structure StmtBlockDemandPreservationKernel where
  stmt :
    ∀ {Γ Δ : TypeEnv} {st : CppStmt}
      {σ : State} {ctrl : CtrlResult} {σ' : State},
      StmtExecutionDemand Γ σ st ctrl σ' Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ'
  block :
    ∀ {Γ Δ : TypeEnv} {ss : StmtBlock}
      {σ : State} {ctrl : CtrlResult} {σ' : State},
      BlockExecutionDemand Γ σ ss ctrl σ' Δ →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ'

theorem stmt_preservation_from_demand_kernel
    (K : StmtBlockDemandPreservationKernel)
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    (demand : StmtExecutionDemand Γ σ st ctrl σ' Δ) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  K.stmt demand

theorem block_preservation_from_demand_kernel
    (K : StmtBlockDemandPreservationKernel)
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    (demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  K.block demand

/--
Compatibility-aware demand preservation target.

This is the final theorem shape the old `StmtControlRecursorCore` should migrate
toward.  The compatibility proof still connects typing and semantics; the demand
proof supplies path-local safety/readiness obligations.
-/
abbrev StmtControlDemandPreservationTarget
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    (hty : HasTypeStmtCI k Γ st Δ)
    (hstep : BigStepStmt σ st ctrl σ') : Prop :=
  StmtControlCompatible hty hstep →
  StmtExecutionDemand Γ σ st ctrl σ' Δ →
  ScopedTypedStateConcrete Γ σ →
  ScopedTypedStateConcrete Δ σ'

/--
Block analogue of `StmtControlDemandPreservationTarget`.
-/
abbrev BlockControlDemandPreservationTarget
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    (hty : HasTypeBlockCI k Γ ss Δ)
    (hstep : BigStepBlock σ ss ctrl σ') : Prop :=
  BlockControlCompatible hty hstep →
  BlockExecutionDemand Γ σ ss ctrl σ' Δ →
  ScopedTypedStateConcrete Γ σ →
  ScopedTypedStateConcrete Δ σ'

end Cpp
