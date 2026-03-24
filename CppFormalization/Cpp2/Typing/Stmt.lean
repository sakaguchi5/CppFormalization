import CppFormalization.Cpp2.Typing.Expr

/-!
Statement typing.
-/

namespace Cpp

mutual

inductive HasTypeStmt : TypeEnv → CppStmt → TypeEnv → Prop where
  | skip {Γ} :
      HasTypeStmt Γ .skip Γ
  | expr {Γ e τ} :
      HasValueType Γ e τ →
      HasTypeStmt Γ (.exprStmt e) Γ
  | assign {Γ p e τ} :
      HasPlaceType Γ p τ →
      HasValueType Γ e τ →
      HasTypeStmt Γ (.assign p e) Γ
  | declareObjNone {Γ τ x} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasTypeStmt Γ (.declareObj τ x none) (declareTypeObject Γ x τ)
  | declareObjSome {Γ τ x e} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasValueType Γ e τ →
      HasTypeStmt Γ (.declareObj τ x (some e)) (declareTypeObject Γ x τ)
  | declareRef {Γ τ x p} :
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      HasTypeStmt Γ (.declareRef τ x p) (declareTypeRef Γ x τ)
  | seq {Γ Γ₁ Γ₂ s t} :
      HasTypeStmt Γ s Γ₁ →
      HasTypeStmt Γ₁ t Γ₂ →
      HasTypeStmt Γ (.seq s t) Γ₂
  | ite {Γ Γ' c s t} :
      HasValueType Γ c (.base .bool) →
      HasTypeStmt Γ s Γ' →
      HasTypeStmt Γ t Γ' →
      HasTypeStmt Γ (.ite c s t) Γ'
  | whileStmt {Γ c body} :
      HasValueType Γ c (.base .bool) →
      HasTypeStmt Γ body Γ →
      HasTypeStmt Γ (.whileStmt c body) Γ
  | block {Γ ss Δ} :
      HasTypeBlock (pushTypeScope Γ) ss Δ →
      HasTypeStmt Γ (.block ss) Γ
  | breakStmt {Γ} :
      HasTypeStmt Γ .breakStmt Γ
  | continueStmt {Γ} :
      HasTypeStmt Γ .continueStmt Γ
  | returnNone {Γ} :
      HasTypeStmt Γ (.returnStmt none) Γ
  | returnSome {Γ e τ} :
      HasValueType Γ e τ →
      HasTypeStmt Γ (.returnStmt (some e)) Γ

inductive HasTypeBlock : TypeEnv → StmtBlock → TypeEnv → Prop where
  | nil {Γ} :
      HasTypeBlock Γ .nil Γ
  | cons {Γ Γ₁ Γ₂ s ss} :
      HasTypeStmt Γ s Γ₁ →
      HasTypeBlock Γ₁ ss Γ₂ →
      HasTypeBlock Γ (.cons s ss) Γ₂

end


def WellTypedFrom (Γ : TypeEnv) (st : CppStmt) : Prop :=
  ∃ Δ, HasTypeStmt Γ st Δ

end Cpp
