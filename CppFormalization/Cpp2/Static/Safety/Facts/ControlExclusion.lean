import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Static.ScopeDiscipline

/-!
Shared exclusion theorems for top-level `break` / `continue` leakage.
This replaces the old `a.lean` scratch file and centralizes the mutual proofs.
-/

namespace Cpp

private abbrev StmtBreakGoal
    {st : CppStmt}
    (ctrl : CtrlResult) : Prop :=
  ctrl = .breakResult → BreakWellScopedAt 0 st → False

private abbrev BlockBreakGoal
    {ss : StmtBlock}
    (ctrl : CtrlResult) : Prop :=
  ctrl = .breakResult → BreakWellScopedBlockAt 0 ss → False

private abbrev StmtBreakCore : Prop :=
  ∀ {σ st ctrl σ'},
    BigStepStmt σ st ctrl σ' →
      StmtBreakGoal (st := st) ctrl

private abbrev BlockBreakCore : Prop :=
  ∀ {σ ss ctrl σ'},
    BigStepBlock σ ss ctrl σ' →
      BlockBreakGoal (ss := ss) ctrl

-- mutual theorem を使うことで、1つの証明構造で両方を同時に解決します
mutual
  private theorem stmt_break_goal
      {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
      (h : BigStepStmt σ st ctrl σ') :
      StmtBreakGoal (st := st) ctrl :=
    match h with
    | .skip => fun hctrl _ => by cases hctrl
    | .expr _  => fun hctrl _ => by cases hctrl
    | .assign _ _ => fun hctrl _ => by cases hctrl
    | .declareObjNone _ => fun hctrl _ => by cases hctrl
    | .declareObjSome _ _ => fun hctrl _ => by cases hctrl
    | .declareRef _ _ => fun hctrl _ => by cases hctrl
    | .seqNormal hs ht => fun hctrl hsc =>
        stmt_break_goal ht hctrl hsc.2
    | .seqBreak hs => fun _ hsc =>
        stmt_break_goal hs rfl hsc.1
    | .seqContinue _ => fun hctrl _ => by cases hctrl
    | .seqReturn _ => fun hctrl _ => by cases hctrl
    | .iteTrue _ hs => fun hctrl hsc =>
        stmt_break_goal hs hctrl hsc.1
    | .iteFalse _ ht => fun hctrl hsc =>
        stmt_break_goal ht hctrl hsc.2
    | .whileFalse _ => fun hctrl _ => by cases hctrl
    | .whileTrueNormal _ _ hwhile => fun hctrl hsc =>
        stmt_break_goal hwhile hctrl hsc
    | .whileTrueBreak _ hb => fun hctrl _ => by cases hctrl
    | .whileTrueContinue _ _ hwhile => fun hctrl hsc =>
        stmt_break_goal hwhile hctrl hsc
    | .whileTrueReturn _ _ => fun hctrl _ => by cases hctrl
    | .block _ hss _ => fun hctrl hsc =>
        block_break_goal hss hctrl (by simpa [BreakWellScopedAt] using hsc)
    | .breakStmt => fun _ hsc => by
        simp [BreakWellScopedAt] at hsc
    | .continueStmt => fun hctrl _ => by cases hctrl
    | .returnNoneStmt => fun hctrl _ => by cases hctrl
    | .returnSome _ => fun hctrl _ => by cases hctrl

  private theorem block_break_goal
      {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
      (h : BigStepBlock σ ss ctrl σ') :
      BlockBreakGoal (ss := ss) ctrl :=
    match h with
    | .nil => fun hctrl _ => by cases hctrl
    | .consNormal hs hss => fun hctrl hsc =>
        block_break_goal hss hctrl hsc.2
    | .consBreak hs => fun _ hsc =>
        stmt_break_goal hs rfl hsc.1
    | .consContinue _ => fun hctrl _ => by cases hctrl
    | .consReturn _ => fun hctrl _ => by cases hctrl
end


private theorem stmt_block_break_not_scoped_core :
    StmtBreakCore ∧ BlockBreakCore := by
  refine ⟨?_, ?_⟩
  · intro σ st ctrl σ' h
    exact stmt_break_goal h
  · intro σ ss ctrl σ' h
    exact block_break_goal h

theorem stmt_break_not_scoped
    {σ σ' : State} {st : CppStmt}
    (h : BigStepStmt σ st .breakResult σ')
    (hsc : BreakWellScopedAt 0 st) : False := by
  exact stmt_block_break_not_scoped_core.1 h rfl hsc

private theorem block_break_not_scoped
    {σ σ' : State} {ss : StmtBlock}
    (h : BigStepBlock σ ss .breakResult σ')
    (hsc : BreakWellScopedBlockAt 0 ss) : False := by
  exact stmt_block_break_not_scoped_core.2 h rfl hsc



private abbrev StmtContinueGoal
    {st : CppStmt}
    (ctrl : CtrlResult) : Prop :=
  ctrl = .continueResult → ContinueWellScopedAt 0 st → False

private abbrev BlockContinueGoal
    {ss : StmtBlock}
    (ctrl : CtrlResult) : Prop :=
  ctrl = .continueResult → ContinueWellScopedBlockAt 0 ss → False

private abbrev StmtContinueCore : Prop :=
  ∀ {σ st ctrl σ'},
    BigStepStmt σ st ctrl σ' →
      StmtContinueGoal (st := st) ctrl

private abbrev BlockContinueCore : Prop :=
  ∀ {σ ss ctrl σ'},
    BigStepBlock σ ss ctrl σ' →
      BlockContinueGoal (ss := ss) ctrl

mutual
  private theorem stmt_continue_goal
      {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
      (h : BigStepStmt σ st ctrl σ') :
      StmtContinueGoal (st := st) ctrl :=
    match h with
    | .skip => fun hctrl _ => by cases hctrl
    | .expr _ => fun hctrl _ => by cases hctrl
    | .assign _ _ => fun hctrl _ => by cases hctrl
    | .declareObjNone _ => fun hctrl _ => by cases hctrl
    | .declareObjSome _ _ => fun hctrl _ => by cases hctrl
    | .declareRef _ _ => fun hctrl _ => by cases hctrl
    | .seqNormal hs ht => fun hctrl hsc =>
        stmt_continue_goal ht hctrl hsc.2
    | .seqBreak _ => fun hctrl _ => by cases hctrl
    | .seqContinue hs => fun _ hsc =>
        stmt_continue_goal hs rfl hsc.1
    | .seqReturn _ => fun hctrl _ => by cases hctrl
    | .iteTrue _ hs => fun hctrl hsc =>
        stmt_continue_goal hs hctrl hsc.1
    | .iteFalse _ ht => fun hctrl hsc =>
        stmt_continue_goal ht hctrl hsc.2
    | .whileFalse _ => fun hctrl _ => by cases hctrl
    | .whileTrueNormal _ _ hwhile => fun hctrl hsc =>
        stmt_continue_goal hwhile hctrl hsc
    | .whileTrueBreak _ _ => fun hctrl _ => by cases hctrl
    | .whileTrueContinue _ _ hwhile => fun hctrl hsc =>
        stmt_continue_goal hwhile hctrl hsc
    | .whileTrueReturn _ _ => fun hctrl _ => by cases hctrl
    | .block _ hss _ => fun hctrl hsc =>
        block_continue_goal hss hctrl (by
          simpa [ContinueWellScopedAt] using hsc)
    | .breakStmt => fun hctrl _ => by cases hctrl
    | .continueStmt => fun _ hsc => by
        simp [ContinueWellScopedAt] at hsc
    | .returnNoneStmt => fun hctrl _ => by cases hctrl
    | .returnSome _ => fun hctrl _ => by cases hctrl

  private theorem block_continue_goal
      {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
      (h : BigStepBlock σ ss ctrl σ') :
      BlockContinueGoal (ss := ss) ctrl :=
    match h with
    | .nil => fun hctrl _ => by cases hctrl
    | .consNormal hs hss => fun hctrl hsc =>
        block_continue_goal hss hctrl hsc.2
    | .consBreak _ => fun hctrl _ => by cases hctrl
    | .consContinue hs => fun _ hsc =>
        stmt_continue_goal hs rfl hsc.1
    | .consReturn _ => fun hctrl _ => by cases hctrl
end

private theorem stmt_block_continue_not_scoped_core :
    StmtContinueCore ∧ BlockContinueCore := by
  refine ⟨?_, ?_⟩
  · intro σ st ctrl σ' h
    exact stmt_continue_goal h
  · intro σ ss ctrl σ' h
    exact block_continue_goal h

theorem stmt_continue_not_scoped
    {σ σ' : State} {st : CppStmt}
    (h : BigStepStmt σ st .continueResult σ')
    (hsc : ContinueWellScopedAt 0 st) : False := by
  exact stmt_block_continue_not_scoped_core.1 h rfl hsc

private theorem block_continue_not_scoped
    {σ σ' : State} {ss : StmtBlock}
    (h : BigStepBlock σ ss .continueResult σ')
    (hsc : ContinueWellScopedBlockAt 0 ss) : False := by
  exact stmt_block_continue_not_scoped_core.2 h rfl hsc

theorem no_top_continue_from_scope
    {σ σ' : State} {st : CppStmt} :
    ContinueWellScoped st → ¬ BigStepStmt σ st .continueResult σ' := by
  intro hsc h
  exact stmt_continue_not_scoped h hsc

theorem no_top_break_from_scope
    {σ σ' : State} {st : CppStmt} :
    BreakWellScoped st → ¬ BigStepStmt σ st .breakResult σ' := by
  intro hsc h
  exact stmt_break_not_scoped h hsc

/-- A scoped block cannot leak `break` to its caller. -/
theorem no_top_break_from_scoped_block
    {σ σ' : State} {ss : StmtBlock} :
    BreakWellScopedBlockAt 0 ss → ¬ BigStepBlock σ ss .breakResult σ' := by
  intro hsc h
  exact block_break_not_scoped h hsc

/-- A scoped block cannot leak `continue` to its caller. -/
theorem no_top_continue_from_scoped_block
    {σ σ' : State} {ss : StmtBlock} :
    ContinueWellScopedBlockAt 0 ss → ¬ BigStepBlock σ ss .continueResult σ' := by
  intro hsc h
  exact block_continue_not_scoped h hsc

end Cpp
