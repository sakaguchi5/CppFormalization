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
          rcases hentry.adequacy.normalSound hstmt with ⟨out, hout⟩
          refine ⟨blockNormalOut_of_stmtBlockNormalOut out, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, hout]
        returnSound := by
          intro rv σ1 hstepOpened
          rcases B.returnToStmt hstepOpened with ⟨σ2, hstmt⟩
          rcases hentry.adequacy.returnSound hstmt with ⟨out, hout⟩
          refine ⟨blockReturnOut_of_stmtBlockReturnOut out, ?_⟩
          simp [blockBodyProfile_of_bodyClosureBoundaryCI,
            blockBodySummary_of_stmtBodySummary, hout] } }

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

end Cpp
