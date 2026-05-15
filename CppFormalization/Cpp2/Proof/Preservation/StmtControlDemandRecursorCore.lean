import CppFormalization.Cpp2.Proof.Preservation.Demand.ExecutionTrace
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Static.Safety.StateInvariantConcrete
import CppFormalization.Cpp2.Proof.Preservation.Demand.PrimitivePreservation
import CppFormalization.Cpp2.Proof.Preservation.Demand.FullPreservation

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandRecursorCore

A demand-oriented replacement target for the old readiness-transport recursor.

This file intentionally does not introduce an axiom.  It fixes the theorem target
that should replace `readinessTransportNormalCore`:

* preservation consumes path-sensitive execution demand;
* the demand must be aligned with the concrete big-step derivation;
* `seq`, block `cons`, and `while` tail cases use the post-state demand carried
  by the aligned demand evidence, not an unrestricted readiness-transport lemma.

The important implementation detail is that the mutual recursor is written as a
term-style `match` on the alignment evidence.  This follows the existing repo
pattern used for mutually recursive proofs over `BigStepStmt` / `BigStepBlock`:
Lean sees the recursive calls as structurally smaller because they are made on
constructor fields of the matched evidence.
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

/--
Follows-step version of the demand preservation kernel.

This is the kernel actually produced by the recursor in this file.  It is weaker
than `StmtBlockDemandPreservationKernel` in the right way: it only consumes a
path-sensitive demand when that demand is aligned with the concrete big-step
execution being preserved.
-/
structure StmtBlockDemandFollowsPreservationKernel where
  stmt :
    ∀ {Γ Δ : TypeEnv} {st : CppStmt}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
      {hstep : BigStepStmt σ st ctrl σ'},
      StmtDemandFollowsStep demand hstep →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ'
  block :
    ∀ {Γ Δ : TypeEnv} {ss : StmtBlock}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
      {hstep : BigStepBlock σ ss ctrl σ'},
      BlockDemandFollowsStep demand hstep →
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

theorem stmt_preservation_from_demand_follows_kernel
    (K : StmtBlockDemandFollowsPreservationKernel)
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
    {hstep : BigStepStmt σ st ctrl σ'}
    (hfollows : StmtDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  K.stmt hfollows

theorem block_preservation_from_demand_follows_kernel
    (K : StmtBlockDemandFollowsPreservationKernel)
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hfollows : BlockDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  K.block hfollows

/--
Compatibility-aware demand preservation target.

The compatibility proof connects typing and semantics; the demand proof supplies
path-local safety/readiness obligations; the follows-step proof says that the
demand and the concrete execution choose the same path.
-/
abbrev StmtControlDemandPreservationTarget
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    (hty : HasTypeStmtCI k Γ st Δ)
    (hstep : BigStepStmt σ st ctrl σ') : Prop :=
  StmtControlCompatible hty hstep →
  (demand : StmtExecutionDemand Γ σ st ctrl σ' Δ) →
  StmtDemandFollowsStep demand hstep →
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
  (demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ) →
  BlockDemandFollowsStep demand hstep →
  ScopedTypedStateConcrete Γ σ →
  ScopedTypedStateConcrete Δ σ'

/--
Primitive demand preservation packaged as a one-field kernel fragment.

This is not the full recursive kernel.  It is the first axiom-free replacement
step: primitive leaves no longer need any readiness-transport axiom.
-/
theorem primitive_stmt_demand_preservation_goal
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) →
    StmtDemandPreservationGoal Γ Δ st σ .normal σ' :=
  primitive_stmt_preserves_from_demand

/--
Block-statement demand preservation packaged as a kernel fragment.

This closes the block-scope component without `readinessTransportNormalCore`.
-/
theorem block_stmt_demand_preservation_goal
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult} :
    (∀ {Θ : TypeEnv} {σ₀ σ₁ : State},
        TopFrameExtensionOf Γ Θ →
        BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ →
        ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ →
        ScopedTypedStateConcrete Θ σ₁) →
    StmtDemandPreservationGoal Γ Γ (.block ss) σ ctrl σ' := by
  intro hbody hdemand hσ
  exact block_stmt_preserves_from_demand hdemand hbody hσ

mutual

/--
Axiom-free statement preservation by recursion over demand/step alignment.

This is the demand-side analogue of the statement half of
`StmtControlRecursorCore`.  In the `seq`, block, and `while` recursive cases,
the tail state is not reconstructed by an external readiness-transport theorem;
it is obtained from the head/body recursive preservation result and then
consumed by the already-aligned tail demand.
-/
theorem stmt_preservation_from_demand_follows
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
    {hstep : BigStepStmt σ st ctrl σ'}
    (hfollows : StmtDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  match hfollows with
  | .skip =>
      fun hσ => by
        simpa using hσ

  | .exprStmt (hty := hty) (hready := hready) (hval := hval) =>
      fun hσ =>
        exprStmt_preserves_from_demand
          (StmtExecutionDemand.exprStmt hty hready hval) hσ

  | .assign
      (hpty := hpty) (hpready := hpready)
      (hvty := hvty) (heready := heready)
      (hval := hval) (hassign := hassign) =>
      fun hσ =>
        assign_preserves_from_demand
          (StmtExecutionDemand.assign hpty hpready hvty heready hval hassign) hσ

  | .declareObjNone (hfresh := hfresh) (hobj := hobj) (hdecl := hdecl) =>
      fun hσ =>
        declareObjNone_preserves_from_demand
          (StmtExecutionDemand.declareObjNone hfresh hobj hdecl) hσ

  | .declareObjSome
      (hfresh := hfresh) (hobj := hobj)
      (hty := hty) (hready := hready)
      (hval := hval) (hdecl := hdecl) =>
      fun hσ =>
        declareObjSome_preserves_from_demand
          (StmtExecutionDemand.declareObjSome hfresh hobj hty hready hval hdecl) hσ

  | .declareRef
      (hfresh := hfresh) (hpty := hpty)
      (hpready := hpready) (hplace := hplace) (hdecl := hdecl) =>
      fun hσ =>
        declareRef_preserves_from_demand
          (StmtExecutionDemand.declareRef hfresh hpty hpready hplace hdecl) hσ

  | .breakStmt =>
      fun hσ => by
        simpa using hσ

  | .continueStmt =>
      fun hσ => by
        simpa using hσ

  | .returnNone =>
      fun hσ => by
        simpa using hσ

  | .returnSome (hty := hty) (hready := hready) (hval := hval) =>
      fun hσ =>
        returnSome_preserves_from_demand
          (StmtExecutionDemand.returnSome hty hready hval) hσ

  | .seqNormal hfHead hfTail =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfTail
          (stmt_preservation_from_demand_follows hfHead hσ)

  | .seqBreak hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

  | .seqContinue hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

  | .seqReturn hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

  | .iteTrue hfBranch =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfBranch hσ

  | .iteFalse hfBranch =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfBranch hσ

  | .whileFalse =>
      fun hσ => by
        simpa using hσ

  | .whileTrueNormal hfBody hfTail =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfTail
          (stmt_preservation_from_demand_follows hfBody hσ)

  | .whileTrueBreak hfBody =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfBody hσ

  | .whileTrueContinue hfBody hfTail =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfTail
          (stmt_preservation_from_demand_follows hfBody hσ)

  | .whileTrueReturn hfBody =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfBody hσ

  | .block (Γ := Γ) (Θ := Θ) (σ₀ := σ₀) (σ₁ := σ₁)
      (hopen := hopen) (hExt := hExt) (hclose := hclose) hfBody =>
      fun hσ =>
        have hσ₀ : ScopedTypedStateConcrete (pushTypeScope Γ) σ₀ :=
          openScope_preserves_scoped_typed_state_concrete hσ hopen
        have hσ₁ : ScopedTypedStateConcrete Θ σ₁ :=
          block_preservation_from_demand_follows hfBody hσ₀
        closeScope_preserves_outer_from_topFrameExtension hExt hσ₁ hclose

/--
Axiom-free block preservation by recursion over demand/step alignment.
-/
theorem block_preservation_from_demand_follows
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hfollows : BlockDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  match hfollows with
  | .nil =>
      fun hσ => by
        simpa using hσ

  | .consNormal hfHead hfTail =>
      fun hσ =>
        block_preservation_from_demand_follows hfTail
          (stmt_preservation_from_demand_follows hfHead hσ)

  | .consBreak hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

  | .consContinue hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

  | .consReturn hfHead =>
      fun hσ =>
        stmt_preservation_from_demand_follows hfHead hσ

end

/-- The public follows-step preservation kernel produced by the mutual recursor. -/
def stmtBlock_demand_follows_preservation_kernel :
    StmtBlockDemandFollowsPreservationKernel where
  stmt := by
    intro Γ Δ st σ ctrl σ' demand hstep hfollows
    exact stmt_preservation_from_demand_follows hfollows
  block := by
    intro Γ Δ ss σ ctrl σ' demand hstep hfollows
    exact block_preservation_from_demand_follows hfollows

/--
Statement preservation from compatibility, demand, and alignment.

The compatibility argument is intentionally not inspected here.  Once a demand
is known to follow the concrete step, preservation is supplied by the demand
recursor.  Compatibility remains part of the public target because callers often
obtain the aligned demand from typing/compatibility data.
-/
theorem stmt_control_preserves_from_demand_follows
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ st Δ}
    {hstep : BigStepStmt σ st ctrl σ'}
    (_hcomp : StmtControlCompatible hty hstep)
    (demand : StmtExecutionDemand Γ σ st ctrl σ' Δ)
    (hfollows : StmtDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  stmt_preservation_from_demand_follows hfollows

/-- Block preservation from compatibility, demand, and alignment. -/
theorem block_control_preserves_from_demand_follows
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (_hcomp : BlockControlCompatible hty hstep)
    (demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ)
    (hfollows : BlockDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  block_preservation_from_demand_follows hfollows

end Cpp
