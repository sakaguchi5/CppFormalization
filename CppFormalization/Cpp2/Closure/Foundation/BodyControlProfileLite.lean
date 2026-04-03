import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Typing.Stmt

namespace Cpp

/-!
# Closure.Foundation.BodyControlProfileLite

E-lite 第一段階の control profile.

修正点:
- `StmtReadyConcrete -> WellTypedFrom` は一般には偽である。
  特に `seq` readiness は tail を同じ Γ で見ているだけで、
  typing のように post-environment を thread しない。
- したがって lite -> CI 互換で必要な `typed0` は `safe` からではなく
  `profile` から回復する。
- そのため leaf 側に coarse typing payload `typed0` を追加する。
-/


/-- Leaf statement 用の最小 summary. -/
structure StmtLeafSummary (Γ : TypeEnv) (st : CppStmt) : Type where
  typed0 : WellTypedFrom Γ st
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}

mutual

/-- Top-level function body 用 lite control profile. -/
inductive StmtBodyProfileLite : TypeEnv → CppStmt → Type where
  | leaf
      {Γ : TypeEnv} {st : CppStmt} :
      StmtLeafSummary Γ st →
      StmtBodyProfileLite Γ st

  | seq
      {Γ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .normalK Γ s Δ →
      StmtBodyProfileLite Γ s →
      StmtBodyProfileLite Δ t →
      StmtBodyProfileLite Γ (.seq s t)

  | block
      {Γ : TypeEnv} {ss : StmtBlock} :
      BlockBodyProfileLite (pushTypeScope Γ) ss →
      StmtBodyProfileLite Γ (.block ss)

/-- Opened block body 用 lite control profile. -/
inductive BlockBodyProfileLite : TypeEnv → StmtBlock → Type where
  | nil
      {Γ : TypeEnv} :
      BlockBodyProfileLite Γ .nil

  | cons
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .normalK Γ s Δ →
      StmtBodyProfileLite Γ s →
      BlockBodyProfileLite Δ ss →
      BlockBodyProfileLite Γ (.cons s ss)

end

/-! ## old coarse typing recovery from lite profiles -/

mutual
theorem wellTypedFrom_of_profileLite
    {Γ : TypeEnv} {st : CppStmt} :
    StmtBodyProfileLite Γ st → WellTypedFrom Γ st := by
  intro h
  cases h with
  | leaf S =>
      exact S.typed0
  | seq hN _ P₂ =>
      -- hN の型から Δ と s を取得。hN : HasTypeStmtCI ... Γ s Δ
      -- ここで自動生成された s✝ や Δ✝ を使う代わりに、
      -- 既存の定理から型推論に任せるのがスムーズです。
      have htS := normalCI_to_old_stmt hN
      rcases wellTypedFrom_of_profileLite P₂ with ⟨Θ, htT⟩
      exact ⟨Θ, HasTypeStmt.seq htS htT⟩
  | block P =>
      rcases typedBlock_of_profileLite P with ⟨Δ, hΔ⟩
      exact ⟨Γ, HasTypeStmt.block hΔ⟩

theorem typedBlock_of_profileLite
    {Γ : TypeEnv} {ss : StmtBlock} :
    BlockBodyProfileLite Γ ss → ∃ Δ, HasTypeBlock Γ ss Δ := by
  intro h
  cases h with
  | nil =>
      exact ⟨Γ, HasTypeBlock.nil⟩
  | cons hN _ P₂ =>
      have htS := normalCI_to_old_stmt hN
      rcases typedBlock_of_profileLite P₂ with ⟨Θ, htSS⟩
      exact ⟨Θ, HasTypeBlock.cons htS htSS⟩
end

end Cpp
