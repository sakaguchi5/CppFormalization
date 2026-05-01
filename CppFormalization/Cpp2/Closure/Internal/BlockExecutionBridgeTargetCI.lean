import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyWitnessCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI

namespace Cpp

/-!
# Closure.Internal.BlockExecutionBridgeTargetCI

Patch 5 secondary asset: an honest target for the remaining opened block-body
adequacy shell.

`BlockBodyClosureCI.lean` has already made the structural/static/profile/root
and dynamic opened-boundary projections theorem-backed.  The remaining shell is
opened block-body adequacy:

`blockBodyAdequacyScaffoldCI_of_bodyClosureBoundaryCI_opened`

The missing mathematical ingredient is not another static projection.  It is an
operational bridge from actual opened block-body executions back to
statement-level `.block ss` executions, so that the existing top-level
`BodyAdequacyCI` can be reused honestly.

The witness-provider migration adds a data-carrying variant of this bridge.  It
lets the opened block route produce `BlockBodyAdequacyWitnessCI` directly, while
the older proof-only adequacy scaffold remains available by forgetting the
witnesses.
-/

/--
Operational bridge from opened block-body execution to statement-level block
execution.

Only normal and return are included, because `BlockBodyAdequacyCI` only asks for
normal and return soundness.  Break/continue are handled elsewhere by scopedness
and top-level exclusion.
-/
structure OpenedBlockExecutionToStmtBridgeCI
    (σ σ0 : State) (ss : StmtBlock) : Type where
  normalToStmt :
    ∀ {σ1 : State},
      BigStepBlock σ0 ss .normal σ1 →
      ∃ σ2 : State, BigStepStmt σ (.block ss) .normal σ2

  returnToStmt :
    ∀ {rv : Option Value} {σ1 : State},
      BigStepBlock σ0 ss (.returnResult rv) σ1 →
      ∃ σ2 : State, BigStepStmt σ (.block ss) (.returnResult rv) σ2

/--
Witness-producing operational bridge from opened block-body execution to
statement-level block execution.

This is the provider-facing version of `OpenedBlockExecutionToStmtBridgeCI`.
It is mathematically the same bridge, but its output is Type-level data rather
than a `Prop`-level existential, so downstream adequacy providers do not need to
choose a statement execution from an existential.
-/
structure OpenedBlockExecutionToStmtWitnessBridgeCI
    (σ σ0 : State) (ss : StmtBlock) : Type where
  normalToStmt :
    ∀ {σ1 : State},
      BigStepBlock σ0 ss .normal σ1 →
      { σ2 : State // BigStepStmt σ (.block ss) .normal σ2 }

  returnToStmt :
    ∀ {rv : Option Value} {σ1 : State},
      BigStepBlock σ0 ss (.returnResult rv) σ1 →
      { σ2 : State // BigStepStmt σ (.block ss) (.returnResult rv) σ2 }

namespace OpenedBlockExecutionToStmtWitnessBridgeCI

/-- Forget the witness-producing bridge to the older proof-only bridge. -/
def toExecutionToStmtBridge
    {σ σ0 : State} {ss : StmtBlock}
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    OpenedBlockExecutionToStmtBridgeCI σ σ0 ss :=
  { normalToStmt := by
      intro σ1 hstep
      let w := B.normalToStmt hstep
      exact ⟨w.val, w.property⟩
    returnToStmt := by
      intro rv σ1 hstep
      let w := B.returnToStmt hstep
      exact ⟨w.val, w.property⟩ }

end OpenedBlockExecutionToStmtWitnessBridgeCI

/--
Opened block-body adequacy follows from:
- the top-level block boundary, whose `adequacy` knows the statement-level
  `.block ss` profile is sound;
- an operational bridge from opened block-body executions back to statement-level
  block executions.

This is the precise replacement target for the remaining block adequacy shell.
It does not assert that such an operational bridge is always available; it only
shows that once the bridge is supplied, the adequacy scaffold is definable.
-/
noncomputable def blockOpenedAdequacyScaffoldCI_of_executionToStmtBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (_hopen : OpenScope σ σ0)
    (B : OpenedBlockExecutionToStmtBridgeCI σ σ0 ss) :
    BlockOpenedAdequacyScaffoldCI Γ σ0 ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry) :=
  { adequacy :=
      { normalSound := by
          intro σ1 hstepOpened
          rcases B.normalToStmt hstepOpened with ⟨σ2, hstmt⟩
          let w := hentry.adequacy.normalWitness hstmt
          refine ⟨blockNormalOut_of_stmtBlockNormalOut w.val, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, w.property]
        returnSound := by
          intro rv σ1 hstepOpened
          rcases B.returnToStmt hstepOpened with ⟨σ2, hstmt⟩
          let w := hentry.adequacy.returnWitness hstmt
          refine ⟨blockReturnOut_of_stmtBlockReturnOut w.val, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, w.property]
        normalWitness := by
          intro σ1 hstepOpened
          let hstmtEx := B.normalToStmt hstepOpened
          let σ2 := Classical.choose hstmtEx
          have hstmt : BigStepStmt σ (.block ss) .normal σ2 :=
            Classical.choose_spec hstmtEx
          let w := hentry.adequacy.normalWitness hstmt
          refine ⟨blockNormalOut_of_stmtBlockNormalOut w.val, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, w.property]

        returnWitness := by
          intro rv σ1 hstepOpened
          let hstmtEx := B.returnToStmt hstepOpened
          let σ2 := Classical.choose hstmtEx
          have hstmt : BigStepStmt σ (.block ss) (.returnResult rv) σ2 :=
            Classical.choose_spec hstmtEx
          let w := hentry.adequacy.returnWitness hstmt
          refine ⟨blockReturnOut_of_stmtBlockReturnOut w.val, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, w.property] } }

/--
Witness-producing opened block-body adequacy scaffold.

This is the provider-facing analogue of `BlockOpenedAdequacyScaffoldCI`.
-/
structure BlockOpenedAdequacyWitnessScaffoldCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  adequacyWitness : BlockBodyAdequacyWitnessCI Γ σ ss P

namespace BlockOpenedAdequacyWitnessScaffoldCI

/-- Forget the witness-producing opened block scaffold to the proof-only scaffold. -/
def toOpenedAdequacyScaffoldCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyControlProfile Γ ss}
    (S : BlockOpenedAdequacyWitnessScaffoldCI Γ σ ss P) :
    BlockOpenedAdequacyScaffoldCI Γ σ ss P :=
  { adequacy := S.adequacyWitness.toBlockBodyAdequacy }

end BlockOpenedAdequacyWitnessScaffoldCI

/--
Build opened block-body adequacy witnesses from statement-level block adequacy
witnesses and a witness-producing execution bridge.

This is the non-classical core of the block witness route.  It still relies on
the block payload projection functions, but it no longer chooses profile outputs
from `BodyAdequacyCI.normalSound` / `returnSound`.
-/
noncomputable def blockBodyAdequacyWitnessCI_of_stmtBlockAdequacyWitness_and_executionBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (_ : OpenScope σ σ0)
    (A : BodyAdequacyWitnessCI Γ σ (.block ss) hentry.static.profile)
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    BlockBodyAdequacyWitnessCI Γ σ0 ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry) :=
  { normalWitness := by
      intro σ1 hstepOpened
      let hstmt := B.normalToStmt hstepOpened
      let w := A.normalWitness hstmt.property
      exact
        ⟨blockNormalOut_of_stmtBlockNormalOut w.val,
          by
            simp [blockBodyProfile_of_bodyClosureBoundaryCI,
              blockBodySummary_of_stmtBodySummary, w.property]⟩
    returnWitness := by
      intro rv σ1 hstepOpened
      let hstmt := B.returnToStmt hstepOpened
      let w := A.returnWitness hstmt.property
      exact
        ⟨blockReturnOut_of_stmtBlockReturnOut w.val,
          by
            simp [blockBodyProfile_of_bodyClosureBoundaryCI,
              blockBodySummary_of_stmtBodySummary, w.property]⟩ }

/--
Opened block-body adequacy witness scaffold from an explicit statement-level
adequacy witness and a witness-producing execution bridge.
-/
noncomputable def blockOpenedAdequacyWitnessScaffoldCI_of_stmtAdequacyWitness_and_executionToStmtWitnessBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ0)
    (A : BodyAdequacyWitnessCI Γ σ (.block ss) hentry.static.profile)
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    BlockOpenedAdequacyWitnessScaffoldCI Γ σ0 ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry) :=
  { adequacyWitness :=
      blockBodyAdequacyWitnessCI_of_stmtBlockAdequacyWitness_and_executionBridge
        hentry hopen A B }

/--
Compatibility route from the existing proof-only top-level boundary to an opened
block-body adequacy witness scaffold.

This adapter is intentionally noncomputable because the top-level
`BodyClosureBoundaryCI` still stores proof-only `BodyAdequacyCI`.  It lets the
block witness route be used before the final destructive replacement of
`BodyAdequacyCI`.
-/
noncomputable def blockOpenedAdequacyWitnessScaffoldCI_of_executionToStmtWitnessBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ0)
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    BlockOpenedAdequacyWitnessScaffoldCI Γ σ0 ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry) :=
  blockOpenedAdequacyWitnessScaffoldCI_of_stmtAdequacyWitness_and_executionToStmtWitnessBridge
    hentry hopen
    (BodyAdequacyWitnessCI.ofBodyAdequacy hentry.adequacy)
    B

/--
Proof-only opened block adequacy scaffold obtained by forgetting the
witness-producing execution bridge route.
-/
noncomputable def blockOpenedAdequacyScaffoldCI_of_executionToStmtWitnessBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ0)
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    BlockOpenedAdequacyScaffoldCI Γ σ0 ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry) :=
  (blockOpenedAdequacyWitnessScaffoldCI_of_executionToStmtWitnessBridge
    hentry hopen B).toOpenedAdequacyScaffoldCI

/--
Assemble an opened `BlockBodyClosureBoundaryCI` using the operational bridge
instead of the old opened-adequacy shell.

This mirrors `blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened`, but
the adequacy component is obtained from
`blockOpenedAdequacyScaffoldCI_of_executionToStmtBridge`.
-/
noncomputable def blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened_via_executionBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ0)
    (B : OpenedBlockExecutionToStmtBridgeCI σ σ0 ss) :
    BlockBodyClosureBoundaryCI Γ σ0 ss :=
  { structural :=
      blockBodyStructuralBoundary_of_bodyClosureBoundaryCI hentry
    static :=
      blockBodyStaticBoundary_of_bodyClosureBoundaryCI hentry
    dynamic :=
      blockBodyDynamicBoundary_of_bodyClosureBoundaryCI_opened hentry hopen
    adequacy := by
      simpa [blockBodyStaticBoundary_of_bodyClosureBoundaryCI_profile hentry] using
        (blockOpenedAdequacyScaffoldCI_of_executionToStmtBridge
          hentry hopen B).adequacy }

/--
Assemble an opened `BlockBodyClosureBoundaryCI` using the witness-producing
execution bridge.
-/
noncomputable def blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened_via_executionWitnessBridge
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ0)
    (B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss) :
    BlockBodyClosureBoundaryCI Γ σ0 ss :=
  { structural :=
      blockBodyStructuralBoundary_of_bodyClosureBoundaryCI hentry
    static :=
      blockBodyStaticBoundary_of_bodyClosureBoundaryCI hentry
    dynamic :=
      blockBodyDynamicBoundary_of_bodyClosureBoundaryCI_opened hentry hopen
    adequacy := by
      simpa [blockBodyStaticBoundary_of_bodyClosureBoundaryCI_profile hentry] using
        ((blockOpenedAdequacyWitnessScaffoldCI_of_executionToStmtWitnessBridge
          hentry hopen B).adequacyWitness.toBlockBodyAdequacy) }

/--
Callback-based block statement closure using an explicit opened-execution bridge.

This is the statement-level assembly route that avoids calling
`blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened`, and therefore
does not depend on the old opened adequacy shell.
-/
theorem block_function_body_closure_boundary_ci_from_opened_body_via_executionBridge
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (openedBridge :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        OpenedBlockExecutionToStmtBridgeCI σ σ0 ss)
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        OpenedBlockExecutionToStmtBridgeCI σ σ0 ss →
        BlockBodyClosureBoundaryCI Γ σ0 ss →
        FunctionBlockBodyClosureResult σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  let σ0 : State := pushScope σ
  have hopen : OpenScope σ σ0 := by
    rfl
  let B : OpenedBlockExecutionToStmtBridgeCI σ σ0 ss :=
    openedBridge hopen
  let hopenedBoundary : BlockBodyClosureBoundaryCI Γ σ0 ss :=
    blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened_via_executionBridge
      hentry hopen B
  have hres : FunctionBlockBodyClosureResult σ0 ss :=
    openedClosure hopen B hopenedBoundary
  exact block_function_body_result_of_opened_block_body_result hopen hres

/--
Callback-based block statement closure using the witness-producing opened
execution bridge.
-/
theorem block_function_body_closure_boundary_ci_from_opened_body_via_executionWitnessBridge
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (openedBridge :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss)
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss →
        BlockBodyClosureBoundaryCI Γ σ0 ss →
        FunctionBlockBodyClosureResult σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  let σ0 : State := pushScope σ
  have hopen : OpenScope σ σ0 := by
    rfl
  let B : OpenedBlockExecutionToStmtWitnessBridgeCI σ σ0 ss :=
    openedBridge hopen
  let hopenedBoundary : BlockBodyClosureBoundaryCI Γ σ0 ss :=
    blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened_via_executionWitnessBridge
      hentry hopen B
  have hres : FunctionBlockBodyClosureResult σ0 ss :=
    openedClosure hopen B hopenedBoundary
  exact block_function_body_result_of_opened_block_body_result hopen hres

end Cpp
