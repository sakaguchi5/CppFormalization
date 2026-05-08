import CppFormalization.Cpp2.Typing.Stmt
import CppFormalization.Cpp2.Static.Inversions
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Semantics.Stmt

/-!
# Closure.Internal.NormalPathTypingBridge

`HasTypeStmt` から `HasTypeStmtCI .normalK` への総橋は置かない。
while / block では old typing だけでは CI normal typing に必要な情報が足りないからである。

ここで固定するのは、次の二種類の「honest な」橋だけである。

1. primitive 文では old normal typing からそのまま CI normal typing へ移れる。
2. seq / ite / block / while では、actual normal step に沿った path data を取り出せる。

このファイルは closure 主線のための case-driven bridge 層であり、
大きな総定理を主張しない。
-/

namespace Cpp

/-! ## primitive 文: old normal typing -> CI normal typing -/

theorem old_skip_to_normalCI
    {Γ Δ : TypeEnv}
    (hty : HasTypeStmt Γ .skip Δ) :
    Δ = Γ ∧ HasTypeStmtCI .normalK Γ .skip Γ := by
  cases hty with
  | skip => exact ⟨rfl, HasTypeStmtCI.skip⟩

theorem old_expr_to_normalCI
    {Γ Δ : TypeEnv} {e : ValExpr}
    (hty : HasTypeStmt Γ (.exprStmt e) Δ) :
    Δ = Γ ∧ ∃ τ, HasValueType Γ e τ ∧ HasTypeStmtCI .normalK Γ (.exprStmt e) Γ := by
  cases hty with
  | expr hv => exact ⟨rfl, _, hv, HasTypeStmtCI.exprStmt hv⟩

theorem old_assign_to_normalCI
    {Γ Δ : TypeEnv} {p : PlaceExpr} {e : ValExpr}
    (hty : HasTypeStmt Γ (.assign p e) Δ) :
    Δ = Γ ∧ ∃ τ, HasPlaceType Γ p τ ∧ HasValueType Γ e τ ∧
      HasTypeStmtCI .normalK Γ (.assign p e) Γ := by
  cases hty with
  | assign hp hv => exact ⟨rfl, _, hp, hv, HasTypeStmtCI.assign hp hv⟩

/-! ### declaration normal payloads -/

/-- Prop-level normal CI payload for object declaration without initializer. -/
structure DeclareObjNoneNormalCIPropPayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) : Prop where
  fresh : currentTypeScopeFresh Γ x
  objectType : ObjectType τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareObj τ x none)
      (declareTypeObject Γ x τ)

/-- Prop-level normal CI payload for object declaration with initializer. -/
structure DeclareObjSomeNormalCIPropPayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) (e : ValExpr) : Prop where
  fresh : currentTypeScopeFresh Γ x
  objectType : ObjectType τ
  valueType : HasValueType Γ e τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareObj τ x (some e))
      (declareTypeObject Γ x τ)

/-- Prop-level normal CI payload for reference declaration. -/
structure DeclareRefNormalCIPropPayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) (p : PlaceExpr) : Prop where
  fresh : currentTypeScopeFresh Γ x
  placeType : HasPlaceType Γ p τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareRef τ x p)
      (declareTypeRef Γ x τ)

/-- Type-level normal CI payload for object declaration without initializer. -/
structure DeclareObjNoneNormalCITypePayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) : Type where
  fresh : currentTypeScopeFresh Γ x
  objectType : ObjectType τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareObj τ x none)
      (declareTypeObject Γ x τ)

/-- Type-level normal CI payload for object declaration with initializer. -/
structure DeclareObjSomeNormalCITypePayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) (e : ValExpr) : Type where
  fresh : currentTypeScopeFresh Γ x
  objectType : ObjectType τ
  valueType : HasValueType Γ e τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareObj τ x (some e))
      (declareTypeObject Γ x τ)

/-- Type-level normal CI payload for reference declaration. -/
structure DeclareRefNormalCITypePayload
    (Γ : TypeEnv) (τ : CppType) (x : Ident) (p : PlaceExpr) : Type where
  fresh : currentTypeScopeFresh Γ x
  placeType : HasPlaceType Γ p τ
  normalCI :
    HasTypeStmtCI .normalK Γ
      (.declareRef τ x p)
      (declareTypeRef Γ x τ)

namespace DeclareObjNoneNormalCITypePayload

/-- Forget a Type-level object-declaration payload to its Prop-level view. -/
def toProp
    {Γ : TypeEnv} {τ : CppType} {x : Ident}
    (P : DeclareObjNoneNormalCITypePayload Γ τ x) :
    DeclareObjNoneNormalCIPropPayload Γ τ x :=
  { fresh := P.fresh
    objectType := P.objectType
    normalCI := P.normalCI }

end DeclareObjNoneNormalCITypePayload

namespace DeclareObjSomeNormalCITypePayload

/-- Forget a Type-level initialized object-declaration payload to its Prop-level view. -/
def toProp
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (P : DeclareObjSomeNormalCITypePayload Γ τ x e) :
    DeclareObjSomeNormalCIPropPayload Γ τ x e :=
  { fresh := P.fresh
    objectType := P.objectType
    valueType := P.valueType
    normalCI := P.normalCI }

end DeclareObjSomeNormalCITypePayload

namespace DeclareRefNormalCITypePayload

/-- Forget a Type-level reference-declaration payload to its Prop-level view. -/
def toProp
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (P : DeclareRefNormalCITypePayload Γ τ x p) :
    DeclareRefNormalCIPropPayload Γ τ x p :=
  { fresh := P.fresh
    placeType := P.placeType
    normalCI := P.normalCI }

end DeclareRefNormalCITypePayload

/--
Declaration-normal payload extracted from old typing for object declaration
without initializer.
-/
theorem old_declareObjNone_to_normalCI_payload
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident}
    (hty : HasTypeStmt Γ (.declareObj τ x none) Δ) :
    Δ = declareTypeObject Γ x τ ∧
      DeclareObjNoneNormalCIPropPayload Γ τ x := by
  cases hty with
  | declareObjNone hfresh hobj =>
      exact
        ⟨rfl,
          { fresh := hfresh
            objectType := hobj
            normalCI := HasTypeStmtCI.declareObjNone hfresh hobj }⟩

/--
Compatibility surface: old declaration-normal bridge with an existential
conclusion.  Prefer `old_declareObjNone_to_normalCI_payload` in new code.
-/
theorem old_declareObjNone_to_normalCI
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident}
    (hty : HasTypeStmt Γ (.declareObj τ x none) Δ) :
    Δ = declareTypeObject Γ x τ ∧
    ∃ (_ : currentTypeScopeFresh Γ x) (_ : ObjectType τ),
      HasTypeStmtCI .normalK Γ (.declareObj τ x none) (declareTypeObject Γ x τ) := by
  rcases old_declareObjNone_to_normalCI_payload hty with ⟨hΔ, P⟩
  exact ⟨hΔ, P.fresh, P.objectType, P.normalCI⟩

/--
Declaration-normal payload extracted from old typing for object declaration with
initializer.
-/
theorem old_declareObjSome_to_normalCI_payload
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hty : HasTypeStmt Γ (.declareObj τ x (some e)) Δ) :
    Δ = declareTypeObject Γ x τ ∧
      DeclareObjSomeNormalCIPropPayload Γ τ x e := by
  cases hty with
  | declareObjSome hfresh hobj hv =>
      exact
        ⟨rfl,
          { fresh := hfresh
            objectType := hobj
            valueType := hv
            normalCI := HasTypeStmtCI.declareObjSome hfresh hobj hv }⟩

/--
Compatibility surface: old initialized declaration-normal bridge with an
existential conclusion.  Prefer `old_declareObjSome_to_normalCI_payload` in new
code.
-/
theorem old_declareObjSome_to_normalCI
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hty : HasTypeStmt Γ (.declareObj τ x (some e)) Δ) :
    Δ = declareTypeObject Γ x τ ∧
    ∃ (_ : currentTypeScopeFresh Γ x) (_ : ObjectType τ) (_ : HasValueType Γ e τ),
      HasTypeStmtCI .normalK Γ (.declareObj τ x (some e)) (declareTypeObject Γ x τ) := by
  rcases old_declareObjSome_to_normalCI_payload hty with ⟨hΔ, P⟩
  exact ⟨hΔ, P.fresh, P.objectType, P.valueType, P.normalCI⟩

/-- Declaration-normal payload extracted from old typing for reference declaration. -/
theorem old_declareRef_to_normalCI_payload
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hty : HasTypeStmt Γ (.declareRef τ x p) Δ) :
    Δ = declareTypeRef Γ x τ ∧
      DeclareRefNormalCIPropPayload Γ τ x p := by
  cases hty with
  | declareRef hfresh hp =>
      exact
        ⟨rfl,
          { fresh := hfresh
            placeType := hp
            normalCI := HasTypeStmtCI.declareRef hfresh hp }⟩

/--
Compatibility surface: old reference declaration-normal bridge with an
existential conclusion.  Prefer `old_declareRef_to_normalCI_payload` in new code.
-/
theorem old_declareRef_to_normalCI
    {Γ Δ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hty : HasTypeStmt Γ (.declareRef τ x p) Δ) :
    Δ = declareTypeRef Γ x τ ∧
    ∃ (_ : currentTypeScopeFresh Γ x) (_ : HasPlaceType Γ p τ),
      HasTypeStmtCI .normalK Γ (.declareRef τ x p) (declareTypeRef Γ x τ) := by
  rcases old_declareRef_to_normalCI_payload hty with ⟨hΔ, P⟩
  exact ⟨hΔ, P.fresh, P.placeType, P.normalCI⟩

/-! ## seq / ite / block / while: normal path data -/

theorem old_seq_normal_path_data
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (hty : HasTypeStmt Γ (.seq s t) Δ)
    (hstep : BigStepStmt σ (.seq s t) .normal σ') :
    ∃ Θ σ₁,
      HasTypeStmt Γ s Θ ∧
      HasTypeStmt Θ t Δ ∧
      BigStepStmt σ s .normal σ₁ ∧
      BigStepStmt σ₁ t .normal σ' := by
  cases hty with
  | seq htyS htyT =>
      cases hstep with
      | seqNormal hstepS hstepT =>
          exact ⟨_, _, htyS, htyT, hstepS, hstepT⟩

theorem old_ite_true_normal_path_data
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    (hty : HasTypeStmt Γ (.ite c s t) Δ)
    (hcond : BigStepValue σ c (.bool true))
    (hstepS : BigStepStmt σ s .normal σ') :
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmt Γ s Δ ∧
    HasTypeStmt Γ t Δ ∧
    BigStepStmt σ (.ite c s t) .normal σ' := by
  cases hty with
  | ite hc htyS htyT =>
      exact ⟨hc, htyS, htyT, BigStepStmt.iteTrue hcond hstepS⟩

theorem old_ite_false_normal_path_data
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    (hty : HasTypeStmt Γ (.ite c s t) Δ)
    (hcond : BigStepValue σ c (.bool false))
    (hstepT : BigStepStmt σ t .normal σ') :
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmt Γ s Δ ∧
    HasTypeStmt Γ t Δ ∧
    BigStepStmt σ (.ite c s t) .normal σ' := by
  cases hty with
  | ite hc htyS htyT =>
      exact ⟨hc, htyS, htyT, BigStepStmt.iteFalse hcond hstepT⟩

theorem old_block_typing_data
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (hty : HasTypeStmt Γ (.block ss) Δ) :
    Δ = Γ ∧ ∃ Θ, HasTypeBlock (pushTypeScope Γ) ss Θ := by
  cases hty with
  | block hB => exact ⟨rfl, _, hB⟩

theorem old_block_normal_path_data
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeStmt Γ (.block ss) Δ)
    (hstep : BigStepStmt σ (.block ss) .normal σ') :
    Δ = Γ ∧
    ∃ Θ σ₀ σ₁,
      HasTypeBlock (pushTypeScope Γ) ss Θ ∧
      OpenScope σ σ₀ ∧
      BigStepBlock σ₀ ss .normal σ₁ ∧
      CloseScope σ₁ σ' := by
  cases hty with
  | block hB =>
      cases hstep with
      | block hopen hbody hclose =>
          exact ⟨rfl, _, _, _, hB, hopen, hbody, hclose⟩

inductive WhileNormalPathShape (c : ValExpr) (body : CppStmt) : State → State → Prop where
  | falseCase {σ}
      (hcond : BigStepValue σ c (.bool false)) :
      WhileNormalPathShape c body σ σ
  | bodyNormal
      {σ σ₁ σ' : State}
      (hcond : BigStepValue σ c (.bool true))
      (hbody : BigStepStmt σ body .normal σ₁)
      (htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ') :
      WhileNormalPathShape c body σ σ'
  | bodyBreak
      {σ σ₁ : State}
      (hcond : BigStepValue σ c (.bool true))
      (hbody : BigStepStmt σ body .breakResult σ₁) :
      WhileNormalPathShape c body σ σ₁
  | bodyContinue
      {σ σ₁ σ' : State}
      (hcond : BigStepValue σ c (.bool true))
      (hbody : BigStepStmt σ body .continueResult σ₁)
      (htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ') :
      WhileNormalPathShape c body σ σ'

theorem whileNormalPathShape_of_step
    {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hstep : BigStepStmt σ (.whileStmt c body) .normal σ') :
    WhileNormalPathShape c body σ σ' := by
  cases hstep with
  | whileFalse hcond =>
      exact WhileNormalPathShape.falseCase hcond
  | whileTrueNormal hcond hbody htail =>
      exact WhileNormalPathShape.bodyNormal hcond hbody htail
  | whileTrueBreak hcond hbody =>
      exact WhileNormalPathShape.bodyBreak hcond hbody
  | whileTrueContinue hcond hbody htail =>
      exact WhileNormalPathShape.bodyContinue hcond hbody htail

theorem old_while_normal_path_data
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hty : HasTypeStmt Γ (.whileStmt c body) Δ)
    (hstep : BigStepStmt σ (.whileStmt c body) .normal σ') :
    Δ = Γ ∧
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmt Γ body Γ ∧
    WhileNormalPathShape c body σ σ' := by
  cases hty with
  | whileStmt hc hbodyTy =>
      exact ⟨rfl, hc, hbodyTy, whileNormalPathShape_of_step hstep⟩

end Cpp
