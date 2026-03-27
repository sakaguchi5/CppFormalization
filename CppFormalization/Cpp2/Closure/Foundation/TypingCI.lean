
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Foundation.TypingCI

`HasTypeStmtCI` / `HasTypeBlockCI` を closure 主線の本体 judgment に昇格させる。

今回の切り替えで重要なのは次の 3 点。

1. typing は control-indexed である。
2. statement は multi-exit relation であり、同じ statement に複数の control judgement が立ってよい。
3. ただし post-environment は path-sensitive なので、abrupt control では同一 statement に
   複数の異なる post-environment が立ちうる。したがって preservation 側では
   「どの typing 導出が実行導出に対応しているか」を別に管理する必要がある。

旧 `HasTypeStmt` / `HasTypeBlock` は normal-path の忘却像として残る。
while / block は old judgement より強い情報を要求するため、
old から new への総橋渡しはここでは置かない。
-/

inductive ControlKind where
  | normalK
  | breakK
  | continueK
  | returnK
  deriving DecidableEq, Repr

/--
`TopFrameExtensionOf Γ Θ` は、
block body を open scope の内側で実行したあとに得られる環境 `Θ` が、
外側 `Γ` に対する top-frame extension であることを表す抽象境界語彙。
-/
axiom TopFrameExtensionOf : TypeEnv → TypeEnv → Prop

mutual

inductive HasTypeStmtCI : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop where
  | skip
      {Γ : TypeEnv} :
      HasTypeStmtCI .normalK Γ .skip Γ

  | exprStmt
      {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
      HasValueType Γ e τ →
      HasTypeStmtCI .normalK Γ (.exprStmt e) Γ

  | assign
      {Γ : TypeEnv} {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      HasPlaceType Γ p τ →
      HasValueType Γ e τ →
      HasTypeStmtCI .normalK Γ (.assign p e) Γ

  | declareObjNone
      {Γ : TypeEnv} {τ : CppType} {x : Ident} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasTypeStmtCI .normalK Γ (.declareObj τ x none) (declareTypeObject Γ x τ)

  | declareObjSome
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasValueType Γ e τ →
      HasTypeStmtCI .normalK Γ (.declareObj τ x (some e)) (declareTypeObject Γ x τ)

  | declareRef
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      HasTypeStmtCI .normalK Γ (.declareRef τ x p) (declareTypeRef Γ x τ)

  | breakStmt
      {Γ : TypeEnv} :
      HasTypeStmtCI .breakK Γ .breakStmt Γ

  | continueStmt
      {Γ : TypeEnv} :
      HasTypeStmtCI .continueK Γ .continueStmt Γ

  | returnNone
      {Γ : TypeEnv} :
      HasTypeStmtCI .returnK Γ (.returnStmt none) Γ

  | returnSome
      {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
      HasValueType Γ e τ →
      HasTypeStmtCI .returnK Γ (.returnStmt (some e)) Γ

  | seq_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .normalK Γ s Θ →
      HasTypeStmtCI k Θ t Δ →
      HasTypeStmtCI k Γ (.seq s t) Δ

  | seq_break
      {Γ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .breakK Γ s Δ →
      HasTypeStmtCI .breakK Γ (.seq s t) Δ

  | seq_continue
      {Γ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .continueK Γ s Δ →
      HasTypeStmtCI .continueK Γ (.seq s t) Δ

  | seq_return
      {Γ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .returnK Γ s Δ →
      HasTypeStmtCI .returnK Γ (.seq s t) Δ

  | ite
      {k : ControlKind} {Γ Δ : TypeEnv}
      {c : ValExpr} {s t : CppStmt} :
      HasValueType Γ c (.base .bool) →
      HasTypeStmtCI k Γ s Δ →
      HasTypeStmtCI k Γ t Δ →
      HasTypeStmtCI k Γ (.ite c s t) Δ

  | while_normal
      {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
      HasValueType Γ c (.base .bool) →
      HasTypeStmtCI .normalK Γ body Γ →
      HasTypeStmtCI .breakK Γ body Γ →
      HasTypeStmtCI .continueK Γ body Γ →
      HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ

  | while_return
      {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
      HasValueType Γ c (.base .bool) →
      HasTypeStmtCI .normalK Γ body Γ →
      HasTypeStmtCI .breakK Γ body Γ →
      HasTypeStmtCI .continueK Γ body Γ →
      HasTypeStmtCI .returnK Γ body Δ →
      HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ

  | block
      {k : ControlKind} {Γ Θ : TypeEnv} {ss : StmtBlock} :
      TopFrameExtensionOf Γ Θ →
      HasTypeBlockCI k (pushTypeScope Γ) ss Θ →
      HasTypeStmtCI k Γ (.block ss) Γ

inductive HasTypeBlockCI : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop where
  | nil
      {Γ : TypeEnv} :
      HasTypeBlockCI .normalK Γ .nil Γ

  | cons_normal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .normalK Γ s Θ →
      HasTypeBlockCI k Θ ss Δ →
      HasTypeBlockCI k Γ (.cons s ss) Δ

  | cons_break
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .breakK Γ s Δ →
      HasTypeBlockCI .breakK Γ (.cons s ss) Δ

  | cons_continue
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .continueK Γ s Δ →
      HasTypeBlockCI .continueK Γ (.cons s ss) Δ

  | cons_return
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .returnK Γ s Δ →
      HasTypeBlockCI .returnK Γ (.cons s ss) Δ

end

/-! ## old normal typing への忘却 -/

mutual

theorem normalCI_to_old_stmt
    {Γ Δ : TypeEnv} {st : CppStmt}
    (h : HasTypeStmtCI .normalK Γ st Δ) :
    HasTypeStmt Γ st Δ := by
  cases h with
  | skip =>
      exact HasTypeStmt.skip
  | exprStmt hty =>
      exact HasTypeStmt.expr hty
  | assign hpty hvty =>
      exact HasTypeStmt.assign hpty hvty
  | declareObjNone hfresh hobj =>
      exact HasTypeStmt.declareObjNone hfresh hobj
  | declareObjSome hfresh hobj hv =>
      exact HasTypeStmt.declareObjSome hfresh hobj hv
  | declareRef hfresh hpty =>
      exact HasTypeStmt.declareRef hfresh hpty
  | seq_normal hs ht =>
      exact HasTypeStmt.seq
        (normalCI_to_old_stmt hs)
        (normalCI_to_old_stmt ht)
  | ite hc hs ht =>
      exact HasTypeStmt.ite
        hc
        (normalCI_to_old_stmt hs)
        (normalCI_to_old_stmt ht)
  | while_normal hc hN hB hC =>
      exact HasTypeStmt.whileStmt
        hc
        (normalCI_to_old_stmt hN)
  | block hExt hB =>
      exact HasTypeStmt.block
        (normalCI_to_old_block hB)

theorem normalCI_to_old_block
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (h : HasTypeBlockCI .normalK Γ ss Δ) :
    HasTypeBlock Γ ss Δ := by
  cases h with
  | nil =>
      exact HasTypeBlock.nil
  | cons_normal hs hss =>
      exact HasTypeBlock.cons
        (normalCI_to_old_stmt hs)
        (normalCI_to_old_block hss)

end

/-! ## inversion / data theorems -/

theorem while_normal_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    Δ = Γ ∧
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ := by
  intro h
  cases h with
  | while_normal _ hN hB hC =>
      exact ⟨rfl, hN, hB, hC⟩

theorem while_return_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ →
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ ∧
    HasTypeStmtCI .returnK Γ body Δ := by
  intro h
  cases h with
  | while_return _ hN hB hC hR =>
      exact ⟨hN, hB, hC, hR⟩

theorem block_typing_data_ci
    {k : ControlKind} {Γ : TypeEnv} {ss : StmtBlock} :
    HasTypeStmtCI k Γ (.block ss) Γ →
    ∃ Θ, TopFrameExtensionOf Γ Θ ∧ HasTypeBlockCI k (pushTypeScope Γ) ss Θ := by
  intro h
  cases h with
  | block hExt hB =>
      exact ⟨_, hExt, hB⟩

theorem seq_normal_typing_data_ci
    {k : ControlKind} {Γ Θ : TypeEnv} {s t : CppStmt} :
    HasTypeStmtCI k Γ (.seq s t) Θ →
    (∃ Δ, HasTypeStmtCI .normalK Γ s Δ ∧ HasTypeStmtCI k Δ t Θ) ∨
    (k = .breakK ∧ HasTypeStmtCI .breakK Γ s Θ) ∨
    (k = .continueK ∧ HasTypeStmtCI .continueK Γ s Θ) ∨
    (k = .returnK ∧ HasTypeStmtCI .returnK Γ s Θ) := by
  intro h
  cases h with
  | seq_normal hs ht =>
      exact Or.inl ⟨_, hs, ht⟩
  | seq_break hs =>
      exact Or.inr <| Or.inl ⟨rfl, hs⟩
  | seq_continue hs =>
      exact Or.inr <| Or.inr <| Or.inl ⟨rfl, hs⟩
  | seq_return hs =>
      exact Or.inr <| Or.inr <| Or.inr ⟨rfl, hs⟩

end Cpp
