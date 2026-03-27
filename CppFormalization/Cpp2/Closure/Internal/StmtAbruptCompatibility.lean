import CppFormalization.Cpp2.Closure.Internal.TypingCISeparation
import CppFormalization.Cpp2.Closure.Internal.TypingCINormalExclusion
import CppFormalization.Cpp2.Closure.Internal.StmtControlCompatibility

namespace Cpp

/-!
# Closure.Internal.StmtAbruptCompatibility

この層の目的は二段である。

1. `.breakK` / `.continueK` に型付けされた statement / block は
   top-level `.normal` 実行にはなれないことを示す。
2. そのうえで、head normal の compatibility を外部から受け取る形で、
   `break` / `continue` の compatibility 再構成を与える。

重要なのは、abrupt compatibility は block の `cons_normal` 分岐で
head normal compatibility を必要とすることだ。
したがってこのファイルでは、normal compatibility そのものはまだ作らず、
それを oracle として受け取る helper 層に留める。
-/

abbrev StmtNormalCompatOracle : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt},
    (hty : HasTypeStmtCI .normalK Γ s Δ) →
    (hstep : BigStepStmt σ s .normal σ') →
    StmtControlCompatible hty hstep

mutual

theorem stmt_break_no_normal_step
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .breakK Γ s Δ)
    (hstep : BigStepStmt σ s .normal σ') :
    False := by
  cases hty with
  | breakStmt =>
      -- break 文が normal に終了することはない [cite: 3]
      cases hstep

  | seq_break htyS =>
      -- 前半 s で break する型付けなのに、全体が normal 実行されることはない [cite: 4]
      cases hstep with
      | seqNormal hstepS hstepT =>
          -- s が normal 実行されたという矛盾を再帰的に示す [cite: 5]
          exact stmt_break_no_normal_step htyS hstepS

  | seq_normal htyS htyT =>
      -- 後半 t で break する型付け [cite: 9]
      cases hstep with
      | seqNormal hstepS hstepT =>
          -- s は normal 実行されるが、t が normal 実行されたという矛盾を示す [cite: 10]
          exact stmt_break_no_normal_step htyT hstepT

  | ite hc htyS htyT =>
      cases hstep with
      | iteTrue _ hstepS =>
          -- True 節が normal 実行された矛盾 [cite: 7]
          exact stmt_break_no_normal_step htyS hstepS
      | iteFalse _ hstepT =>
          -- False 節が normal 実行された矛盾 [cite: 8]
          exact stmt_break_no_normal_step htyT hstepT

  | block hExt htyB =>
      cases hstep with
      | block _ hbody _ =>
          -- block 内部 (ss) が normal 実行された矛盾 [cite: 12]
          exact block_break_no_normal_step htyB hbody

theorem block_break_no_normal_step
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .breakK Γ ss Δ)
    (hstep : BigStepBlock σ ss .normal σ') :
    False := by
  cases hty with
  | cons_break htyS =>
      cases hstep with
      | consNormal hstepS hstepT =>
          -- 最初の文 s で break するはずが normal 実行された矛盾 [cite: 14]
          exact stmt_break_no_normal_step htyS hstepS

  | cons_normal htyS htyT =>
      cases hstep with
      | consNormal hstepS hstepT =>
          -- 最初の文 s は normal だが、残りの ss が normal 実行された矛盾 [cite: 16]
          exact block_break_no_normal_step htyT hstepT

end


mutual

theorem stmt_continue_no_normal_step
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .continueK Γ s Δ)
    (hstep : BigStepStmt σ s .normal σ') :
    False := by
  cases hty with
  | continueStmt =>
      -- continue 文が normal に終了することはない [cite: 17]
      cases hstep

  | seq_continue htyS =>
      -- s.seq t において s で continue する型付けの場合 [cite: 18]
      cases hstep with
      | seqNormal hstepS hstepT =>
          -- s が normal 実行されたという矛盾を導く [cite: 19]
          exact stmt_continue_no_normal_step htyS hstepS

  | seq_normal htyS htyT =>
      -- s.seq t において t で continue する型付けの場合 [cite: 20]
      cases hstep with
      | seqNormal hstepS hstepT =>
          -- s は normal だが、t が normal 実行されたという矛盾を導く [cite: 21]
          exact stmt_continue_no_normal_step htyT hstepT

  | ite hc htyS htyT =>
      -- if 文のいずれかの枝で continue する型付けの場合 [cite: 22]
      cases hstep with
      | iteTrue _ hstepS =>
          -- True 節が normal 実行された矛盾 [cite: 23]
          exact stmt_continue_no_normal_step htyS hstepS
      | iteFalse _ hstepT =>
          -- False 節が normal 実行された矛盾 [cite: 24]
          exact stmt_continue_no_normal_step htyT hstepT

  | block hExt htyB =>
      -- block の内部で continue する型付けの場合 [cite: 25]
      cases hstep with
      | block _ hbody _ =>
          -- 内部の ss が normal 実行された矛盾 [cite: 26]
          exact block_continue_no_normal_step htyB hbody

theorem block_continue_no_normal_step
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .continueK Γ ss Δ)
    (hstep : BigStepBlock σ ss .normal σ') :
    False := by
  cases hty with
  | cons_continue htyS =>
      -- ブロックの最初の文 s で continue する型付けの場合 [cite: 27]
      cases hstep with
      | consNormal hstepS hstepT =>
          -- s が normal 実行された矛盾 [cite: 28]
          exact stmt_continue_no_normal_step htyS hstepS

  | cons_normal htyS htyT =>
      -- s は normal だが、残りのブロック ss で continue する型付けの場合 [cite: 29]
      cases hstep with
      | consNormal hstepS hstepT =>
          -- 残りの ss が normal 実行された矛盾 [cite: 30]
          exact block_continue_no_normal_step htyT hstepT

end


mutual

theorem stmt_break_control_compatible_of_normal
    (stmtNormal : StmtNormalCompatOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .breakK Γ s Δ)
    (hstep : BigStepStmt σ s .breakResult σ') :
    StmtControlCompatible hty hstep := by
  cases hty with
  | breakStmt =>
      cases hstep
      exact .breakStmt (Γ := Γ) (σ := σ)

  | seq_break htyS =>
      cases hstep with
      | seqBreak hstepS =>
          rename_i t
          exact .seq_break (t := t)
            (stmt_break_control_compatible_of_normal stmtNormal htyS hstepS)
      | seqNormal hstepS hstepT =>
          exfalso
          exact stmt_break_no_normal_step htyS hstepS

  | seq_normal htyS htyT =>
      cases hstep with
      | seqBreak hstepS =>
          exfalso
          exact stmt_normal_no_break_step htyS hstepS
      | seqNormal hstepS hstepT =>
          rename_i σ₁
          exact .seq_normal (stmtNormal htyS hstepS)
            (stmt_break_control_compatible_of_normal stmtNormal htyT hstepT)

  | ite hc htyS htyT =>
      cases hstep with
      | iteTrue hcond hstepS =>
          rename_i c s t
          exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond) (hstepS := hstepS)
            (stmt_break_control_compatible_of_normal stmtNormal htyS hstepS)
      | iteFalse hcond hstepT =>
          rename_i c s t
          exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond) (hstepT := hstepT)
            (stmt_break_control_compatible_of_normal stmtNormal htyT hstepT)

  | block hExt htyB =>
      cases hstep with
      | block hopen hbody hclose =>
          rename_i Θ ss σ₁ σ₂
          exact .block (hExt := hExt) (hopen := hopen) (hclose := hclose)
            (block_break_control_compatible_of_normal stmtNormal htyB hbody)

theorem block_break_control_compatible_of_normal
    (stmtNormal : StmtNormalCompatOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .breakK Γ ss Δ)
    (hstep : BigStepBlock σ ss .breakResult σ') :
    BlockControlCompatible hty hstep := by
  cases hty with
  | cons_break htyS =>
      cases hstep with
      | consBreak hstepS =>
          rename_i ss
          exact .cons_break (ss := ss)
            (stmt_break_control_compatible_of_normal stmtNormal htyS hstepS)
      | consNormal hstepS hstepT =>
          exfalso
          exact stmt_break_no_normal_step htyS hstepS

  | cons_normal htyS htyT =>
      cases hstep with
      | consBreak hstepS =>
          exfalso
          exact stmt_normal_no_break_step htyS hstepS
      | consNormal hstepS hstepT =>
          rename_i σ₁
          exact .cons_normal (stmtNormal htyS hstepS)
            (block_break_control_compatible_of_normal stmtNormal htyT hstepT)

end


mutual

theorem stmt_continue_control_compatible_of_normal
    (stmtNormal : StmtNormalCompatOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .continueK Γ s Δ)
    (hstep : BigStepStmt σ s .continueResult σ') :
    StmtControlCompatible hty hstep := by
  cases hty with
  | continueStmt =>
      cases hstep
      exact .continueStmt (Γ := Γ) (σ := σ)

  | seq_continue htyS =>
      cases hstep with
      | seqContinue hstepS =>
          rename_i t
          exact .seq_continue (t := t)
            (stmt_continue_control_compatible_of_normal stmtNormal htyS hstepS)
      | seqNormal hstepS hstepT =>
          exfalso
          exact stmt_continue_no_normal_step htyS hstepS
      | _ => exfalso -- その他のケース（break, return等）は型が合わないため

  | seq_normal htyS htyT =>
      cases hstep with
      | seqContinue hstepS =>
          exfalso
          exact stmt_normal_no_continue_step htyS hstepS
      | seqNormal hstepS hstepT =>
          rename_i σ₁
          exact .seq_normal (stmtNormal htyS hstepS)
            (stmt_continue_control_compatible_of_normal stmtNormal htyT hstepT)
      | _ => exfalso

  | ite hc htyS htyT =>
      cases hstep with
      | iteTrue hcond hstepS =>
          rename_i c s t
          exact .ite_true (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond) (hstepS := hstepS)
            (stmt_continue_control_compatible_of_normal stmtNormal htyS hstepS)
      | iteFalse hcond hstepT =>
          rename_i c s t
          exact .ite_false (hc := hc) (htyS := htyS) (htyT := htyT) (hcond := hcond) (hstepT := hstepT)
            (stmt_continue_control_compatible_of_normal stmtNormal htyT hstepT)
      | _ => exfalso

  | block hExt htyB =>
      cases hstep with
      | block hopen hbody hclose =>
          rename_i Θ ss σ₁ σ₂
          exact .block (hExt := hExt) (hopen := hopen) (hclose := hclose)
            (block_continue_control_compatible_of_normal stmtNormal htyB hbody)
      | _ => exfalso

  -- continueK において while の実行結果が continueResult になるケース（whileTrueNormal等）
  -- がもしあれば追加しますが、通常 continue は while 内部で消費されて normal になるため、
  -- 外部への continueK は cases hty で弾かれるか矛盾になります。

theorem block_continue_control_compatible_of_normal
    (stmtNormal : StmtNormalCompatOracle)
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .continueK Γ ss Δ)
    (hstep : BigStepBlock σ ss .continueResult σ') :
    BlockControlCompatible hty hstep := by
  cases hty with
  | cons_continue htyS =>
      cases hstep with
      | consContinue hstepS =>
          rename_i ss
          exact .cons_continue (ss := ss)
            (stmt_continue_control_compatible_of_normal stmtNormal htyS hstepS)
      | consNormal hstepS hstepT =>
          exfalso
          exact stmt_continue_no_normal_step htyS hstepS
      | _ => exfalso

  | cons_normal htyS htyT =>
      cases hstep with
      | consContinue hstepS =>
          exfalso
          exact stmt_normal_no_continue_step htyS hstepS
      | consNormal hstepS hstepT =>
          rename_i σ₁
          exact .cons_normal (stmtNormal htyS hstepS)
            (block_continue_control_compatible_of_normal stmtNormal htyT hstepT)
      | _ => exfalso

end


end Cpp
