import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Lemmas.ExprDeterminism

namespace Cpp

theorem assigns_deterministic {σ p v σ₁ σ₂} (h₁ : Assigns σ p v σ₁) (h₂ : Assigns σ p v σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨a₁, c₁, hp₁, hh₁, ha₁, hvt₁, hs₁⟩
  rcases h₂ with ⟨a₂, c₂, hp₂, hh₂, ha₂, hvt₂, hs₂⟩
  have haeq : a₁ = a₂ := bigStepPlace_deterministic hp₁ hp₂
  subst haeq
  rw [hh₁] at hh₂; cases hh₂
  exact hs₁.trans hs₂.symm


-- aNext が同じなら、オブジェクト宣言後の状態は一意
theorem declaresObjectWithNext_deterministic {σ τ x ov aNext σ₁ σ₂}
    (h₁ : DeclaresObjectWithNext σ τ x ov aNext σ₁)
    (h₂ : DeclaresObjectWithNext σ τ x ov aNext σ₂) : σ₁ = σ₂ := by
  -- h₁ と h₂ を Payload と Policy に分解する
  rcases h₁ with ⟨σcore1, hpayload1, hpolicy1⟩
  rcases h₂ with ⟨σcore2, hpayload2, hpolicy2⟩

  -- 1. σcore1 = σcore2 であることを示す
  -- 両方とも σcore = declareObjectStateCore σ τ x ov なので一意
  rcases hpayload1 with ⟨_, _, _, _, rfl⟩
  rcases hpayload2 with ⟨_, _, _, _, rfl⟩
  -- これで σcore1 と σcore2 が同じ定義に簡約され、同一視される

  -- 2. σ₁ = σ₂ であることを示す
  -- 両方とも σ' = setNext σcore aNext なので一意
  rcases hpolicy1 with ⟨_, rfl⟩
  rcases hpolicy2 with ⟨_, rfl⟩

  rfl

-- スコープ操作の一意性
theorem openScope_deterministic {σ σ₁ σ₂}
    (h₁ : OpenScope σ σ₁) (h₂ : OpenScope σ σ₂) : σ₁ = σ₂ :=
  h₁.trans h₂.symm

theorem closeScope_deterministic {σ σ₁ σ₂}
    (h₁ : CloseScope σ σ₁) (h₂ : CloseScope σ σ₂) : σ₁ = σ₂ := by
  cases h₁.symm.trans h₂
  rfl


theorem declaresRef_deterministic {σ τ x a σ₁ σ₂} (h₁ : DeclaresRef σ τ x a σ₁) (h₂ : DeclaresRef σ τ x a σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨_, _, hh₁, _, _, hs₁⟩
  rcases h₂ with ⟨_, _, hh₂, _, _, hs₂⟩
  exact hs₁.trans hs₂.symm


-- CtrlResult の引数として .normal を追加します
theorem exprStmt_deterministic {σ e σ₁ σ₂}
    (h₁ : BigStepStmt σ (.exprStmt e) .normal σ₁)
    (h₂ : BigStepStmt σ (.exprStmt e) .normal σ₂) : σ₁ = σ₂ := by
  cases h₁
  cases h₂
  rfl

end Cpp
