import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Internal.TypingCISeparation

`HasTypeStmtCI` / `HasTypeBlockCI` における control kind の分離補題。

重要なのは次の 2 点。

1. `.normalK` の post-environment は一意である。
2. `.normalK` / `.breakK` / `.continueK` の 3 種類は同一 statement / block 上で両立しない。

`returnK` は path-sensitive post-environment を許すため、ここでは分離対象に含めない。
-/

mutual

private theorem old_stmt_post_env_unique
    {Γ Δ₁ Δ₂ : TypeEnv} {st : CppStmt}
    (h₁ : HasTypeStmt Γ st Δ₁)
    (h₂ : HasTypeStmt Γ st Δ₂) :
    Δ₁ = Δ₂ := by
  match h₁ with
  | .skip =>
      cases h₂
      rfl
  | .expr _ =>
      cases h₂
      rfl
  | .assign _ _ =>
      cases h₂
      rfl
  | .declareObjNone _ _ =>
      cases h₂
      rfl
  | .declareObjSome _ _ _ =>
      cases h₂
      rfl
  | .declareRef _ _ =>
      cases h₂
      rfl
  | .seq hs ht =>
      cases h₂ with
      | seq hs' ht' =>
          have hmid : _ = _ := old_stmt_post_env_unique hs hs'
          subst hmid
          exact old_stmt_post_env_unique ht ht'
  | .ite _ hs ht =>
      cases h₂ with
      | ite _ hs' ht' =>
          exact old_stmt_post_env_unique hs hs'
  | .whileStmt _ _ =>
      cases h₂
      rfl
  | .block _ =>
      cases h₂
      rfl
  | .breakStmt =>
      cases h₂
      rfl
  | .continueStmt =>
      cases h₂
      rfl
  | .returnNone =>
      cases h₂
      rfl
  | .returnSome _ =>
      cases h₂
      rfl

private theorem old_block_post_env_unique
    {Γ Δ₁ Δ₂ : TypeEnv} {ss : StmtBlock}
    (h₁ : HasTypeBlock Γ ss Δ₁)
    (h₂ : HasTypeBlock Γ ss Δ₂) :
    Δ₁ = Δ₂ := by
  match h₁ with
  | .nil =>
      cases h₂
      rfl
  | .cons hs hss =>
      cases h₂ with
      | cons hs' hss' =>
          have hmid : _ = _ := old_stmt_post_env_unique hs hs'
          subst hmid
          exact old_block_post_env_unique hss hss'

end

theorem stmt_normal_post_env_unique
    {Γ Δ₁ Δ₂ : TypeEnv} {st : CppStmt}
    (h₁ : HasTypeStmtCI .normalK Γ st Δ₁)
    (h₂ : HasTypeStmtCI .normalK Γ st Δ₂) :
    Δ₁ = Δ₂ := by
  exact old_stmt_post_env_unique (normalCI_to_old_stmt h₁) (normalCI_to_old_stmt h₂)

theorem block_normal_post_env_unique
    {Γ Δ₁ Δ₂ : TypeEnv} {ss : StmtBlock}
    (h₁ : HasTypeBlockCI .normalK Γ ss Δ₁)
    (h₂ : HasTypeBlockCI .normalK Γ ss Δ₂) :
    Δ₁ = Δ₂ := by
  exact old_block_post_env_unique (normalCI_to_old_block h₁) (normalCI_to_old_block h₂)

mutual

private theorem stmt_normal_break_excl
    {Γ Δ : TypeEnv} {st : CppStmt}
    (hN : HasTypeStmtCI .normalK Γ st Δ) :
    ∀ {Θ}, HasTypeStmtCI .breakK Γ st Θ → False := by
  intro Θ hB
  match hN with
  | .skip =>
      cases hB
  | .exprStmt _ =>
      cases hB
  | .assign _ _ =>
      cases hB
  | .declareObjNone _ _ =>
      cases hB
  | .declareObjSome _ _ _ =>
      cases hB
  | .declareRef _ _ =>
      cases hB
  | .seq_normal hs ht =>
      cases hB with
      | seq_normal hs' ht' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact stmt_normal_break_excl ht ht'
      | seq_break hs' =>
          exact stmt_normal_break_excl hs hs'
  | .ite _ hs ht =>
      cases hB with
      | ite _ hs' ht' =>
          exact stmt_normal_break_excl hs hs'
  | .while_normal _ _ _ _ =>
      cases hB
  | .block _ hss =>
      cases hB with
      | block _ hss' =>
          exact block_normal_break_excl hss hss'

private theorem block_normal_break_excl
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (hN : HasTypeBlockCI .normalK Γ ss Δ) :
    ∀ {Θ}, HasTypeBlockCI .breakK Γ ss Θ → False := by
  intro Θ hB
  match hN with
  | .nil =>
      cases hB
  | .cons_normal hs hss =>
      cases hB with
      | cons_normal hs' hss' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact block_normal_break_excl hss hss'
      | cons_break hs' =>
          exact stmt_normal_break_excl hs hs'

end

mutual

private theorem stmt_normal_continue_excl
    {Γ Δ : TypeEnv} {st : CppStmt}
    (hN : HasTypeStmtCI .normalK Γ st Δ) :
    ∀ {Θ}, HasTypeStmtCI .continueK Γ st Θ → False := by
  intro Θ hC
  match hN with
  | .skip =>
      cases hC
  | .exprStmt _ =>
      cases hC
  | .assign _ _ =>
      cases hC
  | .declareObjNone _ _ =>
      cases hC
  | .declareObjSome _ _ _ =>
      cases hC
  | .declareRef _ _ =>
      cases hC
  | .seq_normal hs ht =>
      cases hC with
      | seq_normal hs' ht' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact stmt_normal_continue_excl ht ht'
      | seq_continue hs' =>
          exact stmt_normal_continue_excl hs hs'
  | .ite _ hs ht =>
      cases hC with
      | ite _ hs' ht' =>
          exact stmt_normal_continue_excl hs hs'
  | .while_normal _ _ _ _ =>
      cases hC
  | .block _ hss =>
      cases hC with
      | block _ hss' =>
          exact block_normal_continue_excl hss hss'

private theorem block_normal_continue_excl
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (hN : HasTypeBlockCI .normalK Γ ss Δ) :
    ∀ {Θ}, HasTypeBlockCI .continueK Γ ss Θ → False := by
  intro Θ hC
  match hN with
  | .nil =>
      cases hC
  | .cons_normal hs hss =>
      cases hC with
      | cons_normal hs' hss' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact block_normal_continue_excl hss hss'
      | cons_continue hs' =>
          exact stmt_normal_continue_excl hs hs'

end

mutual

private theorem stmt_break_continue_excl
    {Γ Δ : TypeEnv} {st : CppStmt}
    (hB : HasTypeStmtCI .breakK Γ st Δ) :
    ∀ {Θ}, HasTypeStmtCI .continueK Γ st Θ → False := by
  intro Θ hC
  match hB with
  | .breakStmt =>
      cases hC
  | .seq_normal hs ht =>
      cases hC with
      | seq_normal hs' ht' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact stmt_break_continue_excl ht ht'
      | seq_continue hs' =>
          exact stmt_normal_continue_excl hs hs'
  | .seq_break hs =>
      cases hC with
      | seq_normal hs' ht' =>
          exact stmt_normal_break_excl hs' hs
      | seq_continue hs' =>
          exact stmt_break_continue_excl hs hs'
  | .ite _ hs ht =>
      cases hC with
      | ite _ hs' ht' =>
          exact stmt_break_continue_excl hs hs'
  | .block _ hss =>
      cases hC with
      | block _ hss' =>
          exact block_break_continue_excl hss hss'

private theorem block_break_continue_excl
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (hB : HasTypeBlockCI .breakK Γ ss Δ) :
    ∀ {Θ}, HasTypeBlockCI .continueK Γ ss Θ → False := by
  intro Θ hC
  match hB with
  | .cons_normal hs hss =>
      cases hC with
      | cons_normal hs' hss' =>
          have hmid : _ = _ := stmt_normal_post_env_unique hs hs'
          subst hmid
          exact block_break_continue_excl hss hss'
      | cons_continue hs' =>
          exact stmt_normal_continue_excl hs hs'
  | .cons_break hs =>
      cases hC with
      | cons_normal hs' hss' =>
          exact stmt_normal_break_excl hs' hs
      | cons_continue hs' =>
          exact stmt_break_continue_excl hs hs'

end

theorem stmt_not_both_normal_and_break
    {Γ Δ Θ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    HasTypeStmtCI .breakK Γ st Θ →
    False := by
  intro hN hB
  exact stmt_normal_break_excl hN hB

theorem block_not_both_normal_and_break
    {Γ Δ Θ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    HasTypeBlockCI .breakK Γ ss Θ →
    False := by
  intro hN hB
  exact block_normal_break_excl hN hB

theorem stmt_not_both_normal_and_continue
    {Γ Δ Θ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .normalK Γ st Δ →
    HasTypeStmtCI .continueK Γ st Θ →
    False := by
  intro hN hC
  exact stmt_normal_continue_excl hN hC

theorem block_not_both_normal_and_continue
    {Γ Δ Θ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ ss Δ →
    HasTypeBlockCI .continueK Γ ss Θ →
    False := by
  intro hN hC
  exact block_normal_continue_excl hN hC

theorem stmt_not_both_break_and_continue
    {Γ Δ Θ : TypeEnv} {st : CppStmt} :
    HasTypeStmtCI .breakK Γ st Δ →
    HasTypeStmtCI .continueK Γ st Θ →
    False := by
  intro hB hC
  exact stmt_break_continue_excl hB hC

theorem block_not_both_break_and_continue
    {Γ Δ Θ : TypeEnv} {ss : StmtBlock} :
    HasTypeBlockCI .breakK Γ ss Δ →
    HasTypeBlockCI .continueK Γ ss Θ →
    False := by
  intro hB hC
  exact block_break_continue_excl hB hC

end Cpp
