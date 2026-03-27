import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Static.ScopeDiscipline
import CppFormalization.Cpp2.Lemmas.ControlExclusion

namespace Cpp

/-!
# Closure.Internal.TypingCINormalExclusion

`HasTypeStmtCI .normalK` / `HasTypeBlockCI .normalK` は、top-level の `break` / `continue`
漏れを許さない。

ここでは二段で整理する。

1. normal typing から scope discipline (`BreakWellScoped` / `ContinueWellScoped`) を取り出す。
2. `Lemmas.ControlExclusion` と組み合わせて、normal-typed 実行は
   top-level `break` / `continue` になれないことを得る。

この層は次の compatibility 再構成で、
`seq_normal` / `cons_normal` と `seqBreak` / `seqContinue` の曖昧さを潰すのに使う。
-/

mutual

private theorem stmt_break_scope_lift
    {d : Nat} {st : CppStmt} :
    BreakWellScopedAt d st → BreakWellScopedAt (d + 1) st := by
  intro h
  cases st <;> simp [BreakWellScopedAt] at h ⊢
  · exact ⟨stmt_break_scope_lift h.1, stmt_break_scope_lift h.2⟩
  · exact ⟨stmt_break_scope_lift h.1, stmt_break_scope_lift h.2⟩
  · exact stmt_break_scope_lift h
  · exact block_break_scope_lift h


private theorem block_break_scope_lift
    {d : Nat} {ss : StmtBlock} :
    BreakWellScopedBlockAt d ss → BreakWellScopedBlockAt (d + 1) ss := by
  intro h
  cases ss <;> simp [ BreakWellScopedBlockAt] at h ⊢
  exact ⟨stmt_break_scope_lift h.1, block_break_scope_lift h.2⟩

end

mutual

private theorem stmt_continue_scope_lift
    {d : Nat} {st : CppStmt} :
    ContinueWellScopedAt d st → ContinueWellScopedAt (d + 1) st := by
  intro h
  cases st <;> simp [ContinueWellScopedAt] at h ⊢
  · exact ⟨stmt_continue_scope_lift h.1, stmt_continue_scope_lift h.2⟩
  · exact ⟨stmt_continue_scope_lift h.1, stmt_continue_scope_lift h.2⟩
  · exact stmt_continue_scope_lift h
  · exact block_continue_scope_lift h


private theorem block_continue_scope_lift
    {d : Nat} {ss : StmtBlock} :
    ContinueWellScopedBlockAt d ss → ContinueWellScopedBlockAt (d + 1) ss := by
  intro h
  cases ss <;> simp [ ContinueWellScopedBlockAt] at h ⊢
  exact ⟨stmt_continue_scope_lift h.1, block_continue_scope_lift h.2⟩

end

mutual

private theorem stmt_normal_break_scoped
    {Γ Δ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ → BreakWellScoped st := by
  intro h
  cases h with
  | skip => simp [BreakWellScoped, BreakWellScopedAt]
  | exprStmt _ => simp [BreakWellScoped, BreakWellScopedAt]
  | assign _ _ => simp [BreakWellScoped, BreakWellScopedAt]
  | declareObjNone _ _ => simp [BreakWellScoped, BreakWellScopedAt]
  | declareObjSome _ _ _ => simp [BreakWellScoped, BreakWellScopedAt]
  | declareRef _ _ => simp [BreakWellScoped, BreakWellScopedAt]
  | seq_normal hs ht =>
      exact ⟨stmt_normal_break_scoped hs, stmt_normal_break_scoped ht⟩
  | ite _ hs ht =>
      exact ⟨stmt_normal_break_scoped hs, stmt_normal_break_scoped ht⟩
  | while_normal _ hN _ _ =>
      simpa [BreakWellScoped, BreakWellScopedAt] using
        stmt_break_scope_lift (stmt_normal_break_scoped hN)
  | block _ hss =>
      simpa [BreakWellScoped, BreakWellScopedAt] using
        block_normal_break_scoped hss

private theorem block_normal_break_scoped
    {Γ Δ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ → BreakWellScopedBlockAt 0 ss := by
  intro h
  cases h with
  | nil => simp [BreakWellScopedBlockAt]
  | cons_normal hs hss =>
      exact ⟨stmt_normal_break_scoped hs, block_normal_break_scoped hss⟩

end

mutual

private theorem stmt_normal_continue_scoped
    {Γ Δ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ → ContinueWellScoped st := by
  intro h
  cases h with
  | skip => simp [ContinueWellScoped, ContinueWellScopedAt]
  | exprStmt _ => simp [ContinueWellScoped, ContinueWellScopedAt]
  | assign _ _ => simp [ContinueWellScoped, ContinueWellScopedAt]
  | declareObjNone _ _ => simp [ContinueWellScoped, ContinueWellScopedAt]
  | declareObjSome _ _ _ => simp [ContinueWellScoped, ContinueWellScopedAt]
  | declareRef _ _ => simp [ContinueWellScoped, ContinueWellScopedAt]
  | seq_normal hs ht =>
      exact ⟨stmt_normal_continue_scoped hs, stmt_normal_continue_scoped ht⟩
  | ite _ hs ht =>
      exact ⟨stmt_normal_continue_scoped hs, stmt_normal_continue_scoped ht⟩
  | while_normal _ hN _ _ =>
      simpa [ContinueWellScoped, ContinueWellScopedAt] using
        stmt_continue_scope_lift (stmt_normal_continue_scoped hN)
  | block _ hss =>
      simpa [ContinueWellScoped, ContinueWellScopedAt] using
        block_normal_continue_scoped hss

private theorem block_normal_continue_scoped
    {Γ Δ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ → ContinueWellScopedBlockAt 0 ss := by
  intro h
  cases h with
  | nil => simp [ContinueWellScopedBlockAt]
  | cons_normal hs hss =>
      exact ⟨stmt_normal_continue_scoped hs, block_normal_continue_scoped hss⟩

end

theorem stmt_normal_break_well_scoped
    {Γ Δ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ → BreakWellScoped st := by
  intro h
  exact stmt_normal_break_scoped h

theorem block_normal_break_well_scoped
    {Γ Δ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ → BreakWellScopedBlockAt 0 ss := by
  intro h
  exact block_normal_break_scoped h

theorem stmt_normal_continue_well_scoped
    {Γ Δ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ → ContinueWellScoped st := by
  intro h
  exact stmt_normal_continue_scoped h

theorem block_normal_continue_well_scoped
    {Γ Δ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ → ContinueWellScopedBlockAt 0 ss := by
  intro h
  exact block_normal_continue_scoped h

theorem stmt_normal_no_break_step
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    BigStepStmt σ st .breakResult σ' →
    False := by
  intro hty hstep
  exact no_top_break_from_scope (stmt_normal_break_well_scoped hty) hstep

theorem block_normal_no_break_step
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    BigStepBlock σ ss .breakResult σ' →
    False := by
  intro hty hstep
  exact no_top_break_from_scoped_block (block_normal_break_well_scoped hty) hstep

theorem stmt_normal_no_continue_step
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    BigStepStmt σ st .continueResult σ' →
    False := by
  intro hty hstep
  exact no_top_continue_from_scope (stmt_normal_continue_well_scoped hty) hstep

theorem block_normal_no_continue_step
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    BigStepBlock σ ss .continueResult σ' →
    False := by
  intro hty hstep
  exact no_top_continue_from_scoped_block (block_normal_continue_well_scoped hty) hstep

end Cpp
