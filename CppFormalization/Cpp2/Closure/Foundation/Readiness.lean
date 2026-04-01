import CppFormalization.Cpp2.Closure.Foundation.StateBoundary
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Closure.ReadinessConcrete

`PlaceReady / ExprReady / StmtReady` を、現行構文に沿った第一版の具体形へ落とす。

方針:
- `BigStepPlace` / `BigStepValue` そのものを readiness の定義に埋め込まない。
- ただし `deref` のように pointer 先 address の存在が本質な箇所では、
  そのための補助関係 `PtrValueReadyAt` を分離する。
- statement / block readiness は構文に沿って帰納的に定義する。
-/

/-- address `a` に live な `τ`-cell がある。 -/
def CellLiveTyped (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true

/-- address `a` に読み出し可能な `τ`-cell がある。 -/
def CellReadableTyped (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c v,
    σ.heap a = some c ∧
    c.ty = τ ∧
    c.alive = true ∧
    c.value = some v ∧
    ValueCompat v τ

/--
`e` は pointer-to-`τ` value として安全であり、実際に address `a` を指す準備ができている。
ここではまだ big-step 評価可能性を axiomatize し、後で theorem 化する。
-/
axiom PtrValueReadyAt : TypeEnv → State → ValExpr → CppType → Nat → Prop

mutual

inductive PlaceReadyConcrete : TypeEnv → State → PlaceExpr → CppType → Prop where
  | varObject {Γ σ x τ a} :
      lookupDecl Γ x = some (.object τ) →
      lookupBinding σ x = some (.object τ a) →
      CellLiveTyped σ a τ →
      PlaceReadyConcrete Γ σ (.var x) τ
  | varRef {Γ σ x τ a} :
      lookupDecl Γ x = some (.ref τ) →
      lookupBinding σ x = some (.ref τ a) →
      CellLiveTyped σ a τ →
      PlaceReadyConcrete Γ σ (.var x) τ
  | deref {Γ σ e τ a} :
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      PlaceReadyConcrete Γ σ (.deref e) τ

inductive ExprReadyConcrete : TypeEnv → State → ValExpr → CppType → Prop where
  | litBool {Γ σ b} :
      ExprReadyConcrete Γ σ (.litBool b) (.base .bool)
  | litInt {Γ σ n} :
      ExprReadyConcrete Γ σ (.litInt n) (.base .int)
  | load {Γ σ p τ} :
      PlaceReadyConcrete Γ σ p τ →
      (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
      ExprReadyConcrete Γ σ (.load p) τ
  | addrOf {Γ σ p τ} :
      PlaceReadyConcrete Γ σ p τ →
      ExprReadyConcrete Γ σ (.addrOf p) (.ptr τ)
  | add {Γ σ e₁ e₂} :
      ExprReadyConcrete Γ σ e₁ (.base .int) →
      ExprReadyConcrete Γ σ e₂ (.base .int) →
      ExprReadyConcrete Γ σ (.add e₁ e₂) (.base .int)
  | sub {Γ σ e₁ e₂} :
      ExprReadyConcrete Γ σ e₁ (.base .int) →
      ExprReadyConcrete Γ σ e₂ (.base .int) →
      ExprReadyConcrete Γ σ (.sub e₁ e₂) (.base .int)
  | mul {Γ σ e₁ e₂} :
      ExprReadyConcrete Γ σ e₁ (.base .int) →
      ExprReadyConcrete Γ σ e₂ (.base .int) →
      ExprReadyConcrete Γ σ (.mul e₁ e₂) (.base .int)
  | eq {Γ σ e₁ e₂ τ} :
      ExprReadyConcrete Γ σ e₁ τ →
      ExprReadyConcrete Γ σ e₂ τ →
      ExprReadyConcrete Γ σ (.eq e₁ e₂) (.base .bool)
  | lt {Γ σ e₁ e₂} :
      ExprReadyConcrete Γ σ e₁ (.base .int) →
      ExprReadyConcrete Γ σ e₂ (.base .int) →
      ExprReadyConcrete Γ σ (.lt e₁ e₂) (.base .bool)
  | not {Γ σ e} :
      ExprReadyConcrete Γ σ e (.base .bool) →
      ExprReadyConcrete Γ σ (.not e) (.base .bool)

inductive StmtReadyConcrete : TypeEnv → State → CppStmt → Prop where
  | skip {Γ σ} :
      StmtReadyConcrete Γ σ .skip
  | exprStmt {Γ σ e τ} :
      HasValueType Γ e τ →
      ExprReadyConcrete Γ σ e τ →
      StmtReadyConcrete Γ σ (.exprStmt e)
  | assign {Γ σ p e τ} :
      HasPlaceType Γ p τ →
      PlaceReadyConcrete Γ σ p τ →
      HasValueType Γ e τ →
      ExprReadyConcrete Γ σ e τ →
      StmtReadyConcrete Γ σ (.assign p e)
  | declareObjNone {Γ σ τ x} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      StmtReadyConcrete Γ σ (.declareObj τ x none)
  | declareObjSome {Γ σ τ x e} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      HasValueType Γ e τ →
      ExprReadyConcrete Γ σ e τ →
      StmtReadyConcrete Γ σ (.declareObj τ x (some e))
  | declareRef {Γ σ τ x p} :
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      PlaceReadyConcrete Γ σ p τ →
      StmtReadyConcrete Γ σ (.declareRef τ x p)
  | seq {Γ σ s t} :
      StmtReadyConcrete Γ σ s →
      StmtReadyConcrete Γ σ t →
      StmtReadyConcrete Γ σ (.seq s t)
  | ite {Γ σ c s t} :
      HasValueType Γ c (.base .bool) →
      ExprReadyConcrete Γ σ c (.base .bool) →
      StmtReadyConcrete Γ σ s →
      StmtReadyConcrete Γ σ t →
      StmtReadyConcrete Γ σ (.ite c s t)
  | whileStmt {Γ σ c body} :
      HasValueType Γ c (.base .bool) →
      ExprReadyConcrete Γ σ c (.base .bool) →
      StmtReadyConcrete Γ σ body →
      StmtReadyConcrete Γ σ (.whileStmt c body)
  | block {Γ σ ss} :
      BlockReadyConcrete (pushTypeScope Γ) (pushScope σ) ss →
      StmtReadyConcrete Γ σ (.block ss)
  | breakStmt {Γ σ} :
      StmtReadyConcrete Γ σ .breakStmt
  | continueStmt {Γ σ} :
      StmtReadyConcrete Γ σ .continueStmt
  | returnNone {Γ σ} :
      StmtReadyConcrete Γ σ (.returnStmt none)
  | returnSome {Γ σ e τ} :
      HasValueType Γ e τ →
      ExprReadyConcrete Γ σ e τ →
      StmtReadyConcrete Γ σ (.returnStmt (some e))

inductive BlockReadyConcrete : TypeEnv → State → StmtBlock → Prop where
  | nil {Γ σ} :
      BlockReadyConcrete Γ σ .nil
  | cons {Γ σ s ss} :
      StmtReadyConcrete Γ σ s →
      BlockReadyConcrete Γ σ ss →
      BlockReadyConcrete Γ σ (.cons s ss)

end

/-- concrete readiness は abstract readiness に落とせるべきである。 -/
axiom placeReady_of_concrete
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceReadyConcrete Γ σ p τ →
    PlaceReady Γ σ p τ

axiom exprReady_of_concrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    ExprReady Γ σ e τ

axiom stmtReady_of_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    StmtReadyConcrete Γ σ st →
    StmtReady Γ σ st

axiom blockReady_of_concrete
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ ss →
    BlockReady Γ σ ss

/-- concrete 版から old `IdealAssumptions` 相当の安全条件へ戻すならこの方向でやる。 -/
axiom noUninit_of_exprReadyConcrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    NoUninitValue σ e

axiom noInvalidRef_of_exprReadyConcrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    NoInvalidRefValue σ e

axiom noUninit_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    StmtReadyConcrete Γ σ st →
    NoUninitStmt σ st

axiom noInvalidRef_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    StmtReadyConcrete Γ σ st →
    NoInvalidRefStmt σ st

end Cpp
