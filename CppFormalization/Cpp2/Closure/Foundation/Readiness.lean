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
`e` は `τ` へのポインタとして型付いており、実際に address `a` へ評価される。
heap/live 条件は `CellLiveTyped` 側で別に要求する。
-/
def PtrValueReadyAt
    (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) (a : Nat) : Prop :=
  HasValueType Γ e (.ptr τ) ∧
  BigStepValue σ e (.addr a)

@[simp] theorem ptrValueReadyAt_hasType
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {a : Nat}
    (h : PtrValueReadyAt Γ σ e τ a) :
    HasValueType Γ e (.ptr τ) := h.1

@[simp] theorem ptrValueReadyAt_bigStepValue
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} {a : Nat}
    (h : PtrValueReadyAt Γ σ e τ a) :
    BigStepValue σ e (.addr a) := h.2

@[simp] theorem ptrValueReadyAt_addrOf
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} {a : Nat}
    (hp : HasPlaceType Γ p τ)
    (hplace : BigStepPlace σ p a) :
    PtrValueReadyAt Γ σ (.addrOf p) τ a := by
  exact ⟨HasValueType.addrOf hp, BigStepValue.addrOf hplace⟩

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

theorem validPlace_of_readablePlace
    {σ : State} {p : PlaceExpr} :
    ReadablePlace σ p → ValidPlace σ p := by
  intro h
  rcases h with ⟨a, c, v, hplace, hheap, halive, hval⟩
  exact ⟨a, c, hplace, hheap, halive⟩

theorem validPlace_of_placeReadyConcrete
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceReadyConcrete Γ σ p τ → ValidPlace σ p := by
  intro h
  cases h with
  | varObject hdecl hbind hlive =>
      rcases hlive with ⟨c, hheap, hty, halive⟩
      exact ⟨_, c, BigStepPlace.varObject hbind, hheap, halive⟩
  | varRef hdecl hbind hlive =>
      rcases hlive with ⟨c, hheap, hty, halive⟩
      exact ⟨_, c, BigStepPlace.varRef hbind, hheap, halive⟩
  | deref hptr hlive =>
      rcases hptr with ⟨htyPtr, hval⟩
      rcases hlive with ⟨c, hheap, hty, halive⟩
      exact ⟨_, c, BigStepPlace.deref hval hheap halive, hheap, halive⟩

theorem readablePlace_of_exprReadyConcrete_load
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ (.load p) τ → ReadablePlace σ p := by
  intro h
  cases h with
  | load hp hread =>
      rcases hread with ⟨a, hplace, hcell⟩
      rcases hcell with ⟨c, v, hheap, hty, halive, hval, hcompat⟩
      exact ⟨a, c, v, hplace, hheap, halive, hval⟩

theorem noUninit_of_exprReadyConcrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ExprReadyConcrete Γ σ e τ) : NoUninitValue σ e :=
  match h with
  | .litBool => trivial
  | .litInt => trivial
  | .load hp hread =>
      let ⟨a, hplace, c, v, hheap, _hty, halive, hval, _hcompat⟩ := hread
      ⟨a, c, v, hplace, hheap, halive, hval⟩
  | .addrOf hp =>
      validPlace_of_placeReadyConcrete hp
  | .add h1 h2 =>
      ⟨noUninit_of_exprReadyConcrete h1, noUninit_of_exprReadyConcrete h2⟩
  | .sub h1 h2 =>
      ⟨noUninit_of_exprReadyConcrete h1, noUninit_of_exprReadyConcrete h2⟩
  | .mul h1 h2 =>
      ⟨noUninit_of_exprReadyConcrete h1, noUninit_of_exprReadyConcrete h2⟩
  | .eq h1 h2 =>
      ⟨noUninit_of_exprReadyConcrete h1, noUninit_of_exprReadyConcrete h2⟩
  | .lt h1 h2 =>
      ⟨noUninit_of_exprReadyConcrete h1, noUninit_of_exprReadyConcrete h2⟩
  | .not h =>
    let ih := noUninit_of_exprReadyConcrete h
    ih

theorem noInvalidRef_of_exprReadyConcrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ExprReadyConcrete Γ σ e τ) : NoInvalidRefValue σ e :=
  match h with
  | .litBool => trivial
  | .litInt => trivial
  | .load hp hread =>
      validPlace_of_readablePlace (readablePlace_of_exprReadyConcrete_load (.load hp hread))
  | .addrOf hp =>
      validPlace_of_placeReadyConcrete hp
  | .add h1 h2 =>
      ⟨noInvalidRef_of_exprReadyConcrete h1, noInvalidRef_of_exprReadyConcrete h2⟩
  | .sub h1 h2 =>
      ⟨noInvalidRef_of_exprReadyConcrete h1, noInvalidRef_of_exprReadyConcrete h2⟩
  | .mul h1 h2 =>
      ⟨noInvalidRef_of_exprReadyConcrete h1, noInvalidRef_of_exprReadyConcrete h2⟩
  | .eq h1 h2 =>
      ⟨noInvalidRef_of_exprReadyConcrete h1, noInvalidRef_of_exprReadyConcrete h2⟩
  | .lt h1 h2 =>
      ⟨noInvalidRef_of_exprReadyConcrete h1, noInvalidRef_of_exprReadyConcrete h2⟩
  | .not h =>
    let ih := noInvalidRef_of_exprReadyConcrete h
    ih

mutual

theorem bigStepPlace_of_pushScope
    {σ : State} {p : PlaceExpr} {a : Nat} :
    BigStepPlace (pushScope σ) p a →
    BigStepPlace σ p a := by
  intro h
  cases h with
  | varObject hbind =>
      exact BigStepPlace.varObject (by simpa using hbind)
  | varRef hbind =>
      exact BigStepPlace.varRef (by simpa using hbind)
  | deref hval hheap halive =>
      exact BigStepPlace.deref
        (bigStepValue_of_pushScope hval)
        (by simpa [pushScope] using hheap)
        (by simpa [pushScope] using halive)

theorem bigStepValue_of_pushScope
    {σ : State} {e : ValExpr} {v : Value} :
    BigStepValue (pushScope σ) e v →
    BigStepValue σ e v := by
  intro h
  cases h with
  | litBool =>
      exact BigStepValue.litBool
  | litInt =>
      exact BigStepValue.litInt
  | load hplace hheap halive hval =>
      exact BigStepValue.load
        (bigStepPlace_of_pushScope hplace)
        (by simpa [pushScope] using hheap)
        (by simpa [pushScope] using halive)
        (by simpa using hval)
  | addrOf hplace =>
      exact BigStepValue.addrOf (bigStepPlace_of_pushScope hplace)
  | add h1 h2 =>
      exact BigStepValue.add
        (bigStepValue_of_pushScope h1)
        (bigStepValue_of_pushScope h2)
  | sub h1 h2 =>
      exact BigStepValue.sub
        (bigStepValue_of_pushScope h1)
        (bigStepValue_of_pushScope h2)
  | mul h1 h2 =>
      exact BigStepValue.mul
        (bigStepValue_of_pushScope h1)
        (bigStepValue_of_pushScope h2)
  | eq h1 h2 =>
      exact BigStepValue.eq
        (bigStepValue_of_pushScope h1)
        (bigStepValue_of_pushScope h2)
  | lt h1 h2 =>
      exact BigStepValue.lt
        (bigStepValue_of_pushScope h1)
        (bigStepValue_of_pushScope h2)
  | not h =>
      exact BigStepValue.not (bigStepValue_of_pushScope h)

end

theorem validPlace_of_pushScope
    {σ : State} {p : PlaceExpr} :
    ValidPlace (pushScope σ) p →
    ValidPlace σ p := by
  intro h
  rcases h with ⟨a, c, hplace, hheap, halive⟩
  exact ⟨a, c, bigStepPlace_of_pushScope hplace,
    by simpa [pushScope] using hheap,
    by simpa [pushScope] using halive⟩

theorem readablePlace_of_pushScope
    {σ : State} {p : PlaceExpr} :
    ReadablePlace (pushScope σ) p →
    ReadablePlace σ p := by
  intro h
  rcases h with ⟨a, c, v, hplace, hheap, halive, hval⟩
  exact ⟨a, c, v, bigStepPlace_of_pushScope hplace,
    by simpa [pushScope] using hheap,
    by simpa [pushScope] using halive,
    by simpa using hval⟩

theorem noUninitValue_of_pushScope {σ : State} {e : ValExpr} :
    NoUninitValue (pushScope σ) e → NoUninitValue σ e :=
  match e with
  | .litBool _ => fun h => h
  | .litInt _ => fun h => h
  | .load _ => fun h => readablePlace_of_pushScope h
  | .addrOf _ => fun h => validPlace_of_pushScope h
  | .add e1 e2 => fun h =>
      ⟨noUninitValue_of_pushScope (e := e1) h.1, noUninitValue_of_pushScope (e := e2) h.2⟩
  | .sub e1 e2 => fun h =>
      ⟨noUninitValue_of_pushScope (e := e1) h.1, noUninitValue_of_pushScope (e := e2) h.2⟩
  | .mul e1 e2 => fun h =>
      ⟨noUninitValue_of_pushScope (e := e1) h.1, noUninitValue_of_pushScope (e := e2) h.2⟩
  | .eq e1 e2 => fun h =>
      ⟨noUninitValue_of_pushScope (e := e1) h.1, noUninitValue_of_pushScope (e := e2) h.2⟩
  | .lt e1 e2 => fun h =>
      ⟨noUninitValue_of_pushScope (e := e1) h.1, noUninitValue_of_pushScope (e := e2) h.2⟩
  | .not e_inner => fun h =>
      noUninitValue_of_pushScope (e := e_inner) h

theorem noInvalidRefValue_of_pushScope
    {σ : State} {e : ValExpr} :
    NoInvalidRefValue (pushScope σ) e →
    NoInvalidRefValue σ e :=
  match e with
  | .litBool _ => fun h => h
  | .litInt _ => fun h => h
  | .load _ => fun h => validPlace_of_pushScope h
  | .addrOf _ => fun h => validPlace_of_pushScope h
  | .add e1 e2 => fun h =>
      ⟨noInvalidRefValue_of_pushScope (e := e1) h.1, noInvalidRefValue_of_pushScope (e := e2) h.2⟩
  | .sub e1 e2 => fun h =>
      ⟨noInvalidRefValue_of_pushScope (e := e1) h.1, noInvalidRefValue_of_pushScope (e := e2) h.2⟩
  | .mul e1 e2 => fun h =>
      ⟨noInvalidRefValue_of_pushScope (e := e1) h.1, noInvalidRefValue_of_pushScope (e := e2) h.2⟩
  | .eq e1 e2 => fun h =>
      ⟨noInvalidRefValue_of_pushScope (e := e1) h.1, noInvalidRefValue_of_pushScope (e := e2) h.2⟩
  | .lt e1 e2 => fun h =>
      ⟨noInvalidRefValue_of_pushScope (e := e1) h.1, noInvalidRefValue_of_pushScope (e := e2) h.2⟩
  | .not e_inner => fun h =>
      noInvalidRefValue_of_pushScope (e := e_inner) h

mutual

theorem noUninitStmt_of_pushScope
    {σ : State} {st : CppStmt} :
    NoUninitStmt (pushScope σ) st →
    NoUninitStmt σ st :=
  match st with
  | .skip => fun h => h
  | .exprStmt _ => fun h =>
      noUninitValue_of_pushScope h
  | .assign _ _ => fun h =>
      ⟨validPlace_of_pushScope h.1, noUninitValue_of_pushScope h.2⟩
  | .declareObj _ _ none => fun h => h
  | .declareObj _ _ (some _) => fun h =>
      noUninitValue_of_pushScope h
  | .declareRef _ _ _ => fun h =>
      validPlace_of_pushScope h
  | .seq _ _ => fun h =>
      ⟨noUninitStmt_of_pushScope h.1, noUninitStmt_of_pushScope h.2⟩
  | .ite _ _ _ => fun h =>
      ⟨noUninitValue_of_pushScope h.1, noUninitStmt_of_pushScope h.2.1, noUninitStmt_of_pushScope h.2.2⟩
  | .whileStmt _ _ => fun h =>
      ⟨noUninitValue_of_pushScope h.1, noUninitStmt_of_pushScope h.2⟩
  | .block _ => fun h =>
      noUninitBlock_of_pushScope h
  | .breakStmt => fun h => h
  | .continueStmt => fun h => h
  | .returnStmt none => fun h => h
  | .returnStmt (some _) => fun h =>
      noUninitValue_of_pushScope h

theorem noUninitBlock_of_pushScope
    {σ : State} {ss : StmtBlock} :
    NoUninitBlock (pushScope σ) ss →
    NoUninitBlock σ ss :=
  match ss with
  | .nil => fun h => h
  | .cons _ _ => fun h =>
      ⟨noUninitStmt_of_pushScope h.1, noUninitBlock_of_pushScope h.2⟩
end

mutual

theorem noInvalidRefStmt_of_pushScope
    {σ : State} {st : CppStmt} :
    NoInvalidRefStmt (pushScope σ) st →
    NoInvalidRefStmt σ st :=
  match st with
  | .skip => fun h => h
  | .exprStmt _ => fun h =>
      noInvalidRefValue_of_pushScope h
  | .assign _ _ => fun h =>
      ⟨validPlace_of_pushScope h.1, noInvalidRefValue_of_pushScope h.2⟩
  | .declareObj _ _ none => fun h => h
  | .declareObj _ _ (some _) => fun h =>
      noInvalidRefValue_of_pushScope h
  | .declareRef _ _ _ => fun h =>
      validPlace_of_pushScope h
  | .seq _ _ => fun h =>
      ⟨noInvalidRefStmt_of_pushScope h.1, noInvalidRefStmt_of_pushScope h.2⟩
  | .ite _ _ _ => fun h =>
      ⟨noInvalidRefValue_of_pushScope h.1, noInvalidRefStmt_of_pushScope h.2.1, noInvalidRefStmt_of_pushScope h.2.2⟩
  | .whileStmt _ _ => fun h =>
      ⟨noInvalidRefValue_of_pushScope h.1, noInvalidRefStmt_of_pushScope h.2⟩
  | .block _ => fun h =>
      noInvalidRefBlock_of_pushScope h
  | .breakStmt => fun h => h
  | .continueStmt => fun h => h
  | .returnStmt none => fun h => h
  | .returnStmt (some _) => fun h =>
      noInvalidRefValue_of_pushScope h

theorem noInvalidRefBlock_of_pushScope
    {σ : State} {ss : StmtBlock} :
    NoInvalidRefBlock (pushScope σ) ss →
    NoInvalidRefBlock σ ss :=
  match ss with
  | .nil => fun h => h
  | .cons _ _ => fun h =>
      ⟨noInvalidRefStmt_of_pushScope h.1, noInvalidRefBlock_of_pushScope h.2⟩
end

theorem hasPlaceType_of_placeReadyConcrete
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceReadyConcrete Γ σ p τ →
    HasPlaceType Γ p τ := by
  intro h
  cases h with
  | varObject hdecl _ _ =>
      exact HasPlaceType.var hdecl
  | varRef hdecl _ _ =>
      exact HasPlaceType.var hdecl
  | deref hptr _ =>
      exact HasPlaceType.deref hptr.1

theorem placeReady_of_concrete
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceReadyConcrete Γ σ p τ →
    PlaceReady Γ σ p τ := by
  intro h
  exact ⟨hasPlaceType_of_placeReadyConcrete h, validPlace_of_placeReadyConcrete h⟩

theorem hasValueType_of_exprReadyConcrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    HasValueType Γ e τ := fun h =>
  match h with
  | .litBool =>
      HasValueType.litBool
  | .litInt =>
      HasValueType.litInt
  | .load hp _ =>
      HasValueType.load (hasPlaceType_of_placeReadyConcrete hp)
  | .addrOf hp =>
      HasValueType.addrOf (hasPlaceType_of_placeReadyConcrete hp)
  | .add h1 h2 =>
      HasValueType.add
        (hasValueType_of_exprReadyConcrete h1)
        (hasValueType_of_exprReadyConcrete h2)
  | .sub h1 h2 =>
      HasValueType.sub
        (hasValueType_of_exprReadyConcrete h1)
        (hasValueType_of_exprReadyConcrete h2)
  | .mul h1 h2 =>
      HasValueType.mul
        (hasValueType_of_exprReadyConcrete h1)
        (hasValueType_of_exprReadyConcrete h2)
  | .eq h1 h2 =>
      HasValueType.eq
        (hasValueType_of_exprReadyConcrete h1)
        (hasValueType_of_exprReadyConcrete h2)
  | .lt h1 h2 =>
      HasValueType.lt
        (hasValueType_of_exprReadyConcrete h1)
        (hasValueType_of_exprReadyConcrete h2)
  | .not h =>
      HasValueType.not (hasValueType_of_exprReadyConcrete h)

theorem exprReady_of_concrete
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    ExprReady Γ σ e τ := by
  intro h
  exact ⟨
    hasValueType_of_exprReadyConcrete h,
    noUninit_of_exprReadyConcrete h,
    noInvalidRef_of_exprReadyConcrete h
  ⟩

mutual

theorem noUninit_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    StmtReadyConcrete Γ σ st →
    NoUninitStmt σ st := by
  intro h
  cases h with
  | skip =>
      trivial
  | exprStmt _ hE =>
      exact noUninit_of_exprReadyConcrete hE
  | assign _ hP _ hE =>
      exact ⟨validPlace_of_placeReadyConcrete hP, noUninit_of_exprReadyConcrete hE⟩
  | declareObjNone _ _ =>
      trivial
  | declareObjSome _ _ _ hE =>
      exact noUninit_of_exprReadyConcrete hE
  | declareRef _ _ hP =>
      exact validPlace_of_placeReadyConcrete hP
  | seq hS hT =>
      exact ⟨noUninit_of_stmtReadyConcrete hS,
        noUninit_of_stmtReadyConcrete hT⟩
  | ite _ hC hS hT =>
      exact ⟨noUninit_of_exprReadyConcrete hC,
        noUninit_of_stmtReadyConcrete hS,
        noUninit_of_stmtReadyConcrete hT⟩
  | whileStmt _ hC hB =>
      exact ⟨noUninit_of_exprReadyConcrete hC,
        noUninit_of_stmtReadyConcrete hB⟩
  | block hSS =>
      exact noUninitBlock_of_pushScope
        (noUninit_of_blockReadyConcrete hSS)
  | breakStmt =>
      trivial
  | continueStmt =>
      trivial
  | returnNone =>
      trivial
  | returnSome _ hE =>
      exact noUninit_of_exprReadyConcrete hE

theorem noUninit_of_blockReadyConcrete
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ ss →
    NoUninitBlock σ ss := by
  intro h
  cases h with
  | nil =>
      trivial
  | cons hS hSS =>
      exact ⟨noUninit_of_stmtReadyConcrete hS,
        noUninit_of_blockReadyConcrete hSS⟩
end

mutual

theorem noInvalidRef_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    StmtReadyConcrete Γ σ st →
    NoInvalidRefStmt σ st := by
  intro h
  cases h with
  | skip =>
      trivial
  | exprStmt _ hE =>
      exact noInvalidRef_of_exprReadyConcrete hE
  | assign _ hP _ hE =>
      exact ⟨validPlace_of_placeReadyConcrete hP, noInvalidRef_of_exprReadyConcrete hE⟩
  | declareObjNone _ _ =>
      trivial
  | declareObjSome _ _ _ hE =>
      exact noInvalidRef_of_exprReadyConcrete hE
  | declareRef _ _ hP =>
      exact validPlace_of_placeReadyConcrete hP
  | seq hS hT =>
      exact ⟨noInvalidRef_of_stmtReadyConcrete hS,
        noInvalidRef_of_stmtReadyConcrete hT⟩
  | ite _ hC hS hT =>
      exact ⟨noInvalidRef_of_exprReadyConcrete hC,
        noInvalidRef_of_stmtReadyConcrete hS,
        noInvalidRef_of_stmtReadyConcrete hT⟩
  | whileStmt _ hC hB =>
      exact ⟨noInvalidRef_of_exprReadyConcrete hC,
        noInvalidRef_of_stmtReadyConcrete hB⟩
  | block hSS =>
      exact noInvalidRefBlock_of_pushScope
        (noInvalidRef_of_blockReadyConcrete hSS)
  | breakStmt =>
      trivial
  | continueStmt =>
      trivial
  | returnNone =>
      trivial
  | returnSome _ hE =>
      exact noInvalidRef_of_exprReadyConcrete hE

theorem noInvalidRef_of_blockReadyConcrete
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ ss →
    NoInvalidRefBlock σ ss := by
  intro h
  cases h with
  | nil =>
      trivial
  | cons hS hSS =>
      exact ⟨noInvalidRef_of_stmtReadyConcrete hS,
        noInvalidRef_of_blockReadyConcrete hSS⟩
end


end Cpp
