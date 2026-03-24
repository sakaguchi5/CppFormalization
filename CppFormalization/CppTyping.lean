import CppFormalization.CppState
import CppFormalization.CppState_Contracts

namespace Cpp

/-
Phase 2: 静的整形・型付け・State 型整合

三層構造：
  層 A: 値レベルの型整合
        ObjectFitsType, RValueHasType, LValueHasType, CellWellTyped
        → Cell.ty と Cell.object の整合を数学化する

  層 B: 式・文の静的整形
        isAssignable, breakOnlyInLoop, returnTypeConsistent
        noFreeVars, WellFormedExpr, WellFormedStmt
        → 構文的に「おかしい」プログラムを排除する

  層 C: 型付け判断
        HasType (Γ ⊢ e : τ), HasTypeStmt
        → 式・文に型を与える

設計方針：
  - Phase 2 の述語は全て Prop（命題）であり、決定可能かどうかは別問題
  - evaluator（Phase 4）はこれらを前提として受け取る
  - Phase 5 の preservation は「これらが実行で壊れない」を示す
-/

-- ============================================================
-- §A. 値レベルの型整合
-- ============================================================

section ValueTyping

/-
RValueHasType : RValue → CppType → Prop

rvalue が C++ の型 τ を持つことを表す。
理想化：
  - Int は数学的整数 ℤ（符号付き整数型全体に使う）
  - Nat は符号なし整数（uint, size_t 等）
  - Float は float/double 両方をカバー
  - ptr τ はポインタ型 τ* を持つ
-/
inductive RValueHasType : RValue → CppType → Prop where
  | void  :
      RValueHasType .void CVoid

  | int   : ∀ (n : Int),
      RValueHasType (.int n) CInt

  | uint  : ∀ (n : Nat),
      RValueHasType (.uint n) CUInt

  | float : ∀ (x : Float),
      -- float と double は同じ RValue.float で表現（理想化）
      RValueHasType (.float x) CFloat

  | double : ∀ (x : Float),
      RValueHasType (.float x) CDouble

  | bool  : ∀ (b : Bool),
      RValueHasType (.bool b) CBool

  | ptrNonNull : ∀ (l : Loc) (τ : CppType),
      -- l ≠ nullLoc のポインタは τ* 型
      l ≠ nullLoc →
      RValueHasType (.ptr l) (.ptr τ)

  | ptrNull : ∀ (τ : CppType),
      -- nullptr は任意のポインタ型を持てる
      RValueHasType (.ptr nullLoc) (.ptr τ)

/-
ObjectFitsType : Object → CppType → Prop

store 上の object が型 τ と整合することを表す。
これが「Cell.ty と Cell.object の整合の数学化」の中心。
-/
inductive ObjectFitsType : Object → CppType → Prop where
  | scalar : ∀ (v : RValue) (τ : CppType),
      RValueHasType v τ →
      ObjectFitsType (.scalar v) τ

  | array  : ∀ (elemTy : CppType) (locs : List Loc) (n : Nat),
      -- 要素数が型の n と一致する
      locs.length = n →
      ObjectFitsType (.array elemTy locs) (.array elemTy n)

  | struct : ∀ (name : Ident) (fields : List (Ident × Loc)),
      ObjectFitsType (.struct_ name fields) (.named name)

/-
CellWellTyped : Cell → Prop

Cell 一つが内部的に整合していること。
具体的には cell.object が cell.ty と合っていること。
-/
def CellWellTyped (c : Cell) : Prop :=
  ObjectFitsType c.object c.ty

/-
LValueHasType : State → Loc → CppType → Prop

lvalue（場所）が型 τ を持つことを表す。
「場所 l を読んだとき、得られるオブジェクトの型は τ である」という意味。
-/
def LValueHasType (s : State) (l : Loc) (τ : CppType) : Prop :=
  ∃ c : Cell,
    s.readCell l = some c ∧
    c.alive = true ∧
    c.ty = τ ∧
    CellWellTyped c

end ValueTyping

-- ============================================================
-- §B. 型環境
-- ============================================================

section TypeEnvironment

/-
型環境 TyEnv : 変数名 → 型
静的な型検査に使う（runtime の Env とは別物）
-/
abbrev TyEnv := List (Ident × CppType)

namespace TyEnv

def lookup (Γ : TyEnv) (x : Ident) : Option CppType :=
  match Γ.find? (fun p => p.1 == x) with
  | some (_, τ) => some τ
  | none        => none

def extend (Γ : TyEnv) (x : Ident) (τ : CppType) : TyEnv :=
  (x, τ) :: Γ

def extendMany (Γ : TyEnv) : List (Ident × CppType) → TyEnv
  | []            => Γ
  | (x, τ) :: xs => extendMany (Γ.extend x τ) xs

end TyEnv

end TypeEnvironment

-- ============================================================
-- §B'. 静的整形 (Well-Formedness)
-- ============================================================

section WellFormedness

/-
isAssignable : CppExpr → Prop

式が代入の左辺として有効かどうか（静的に判定可能）。
Phase 2 の静的側に置く（Phase 2.5 に置くと概念がぶれる）。

代入可能な式：
  - var x          （変数）
  - deref e        （デリファレンス）
  - index e1 e2    （配列添字）
  - member e f     （メンバアクセス）
  - arrow e f      （ポインタメンバ）
-/
def isAssignable : CppExpr → Prop
  | .var _        => True
  | .deref _      => True
  | .index _ _    => True
  | .member _ _   => True
  | .arrow _ _    => True
  | _             => False

-- isAssignable の決定可能性
instance : DecidablePred isAssignable
  | .var _        => isTrue  trivial
  | .deref _      => isTrue  trivial
  | .index _ _    => isTrue  trivial
  | .member _ _   => isTrue  trivial
  | .arrow _ _    => isTrue  trivial
  | .lit _        => isFalse (fun h => h)
  | .binop _ _ _  => isFalse (fun h => h)
  | .unop _ _     => isFalse (fun h => h)
  | .assign _ _ _ => isFalse (fun h => h)
  | .call _ _     => isFalse (fun h => h)
  | .addrOf _     => isFalse (fun h => h)
  | .ternary _ _ _=> isFalse (fun h => h)
  | .cast _ _     => isFalse (fun h => h)
  | .sizeofExpr _ => isFalse (fun h => h)
  | .sizeofType _ => isFalse (fun h => h)
  | .new_ _ _     => isFalse (fun h => h)
  | .delete_ _    => isFalse (fun h => h)
  | .comma _ _    => isFalse (fun h => h)

/-
breakOnlyInLoop : CppStmt → Bool

break/continue が適切な場所（ループ/switch の内側）にのみ現れるかを確認。
Bool 関数として定義（静的チェックとして実行可能にする）。
-/
mutual
  def breakOnlyInLoop (s : CppStmt) : Bool :=
    checkStmt false s

  private def checkStmt (inLoop : Bool) : CppStmt → Bool
    | .skip           => true
    | .expr _         => true
    | .decl _         => true
    | .return_ _      => true
    | .block ss       => checkStmts inLoop ss
    | .ite _ s1 s2    => checkStmt inLoop s1 && checkStmt inLoop s2
    -- ループ内に入る → inLoop = true に切り替える
    | .while_ _ body  => checkStmt true body
    | .doWhile body _ => checkStmt true body
    | .for_ _ _ _ body   => checkStmt true body
    | .forRange _ _ _ body => checkStmt true body
    -- break/continue はループ内でのみ合法
    | .break_         => inLoop
    | .continue_      => inLoop
    -- switch は break を合法にするが continue は不可
    | .switch_ _ cases => checkSwitchCases cases

  private def checkStmts (inLoop : Bool) : List CppStmt → Bool
    | []       => true
    | s :: ss  => checkStmt inLoop s && checkStmts inLoop ss

  private def checkSwitchCases : List SwitchCase → Bool
    | []                  => true
    | .case_ _ ss :: rest => checkStmts true ss && checkSwitchCases rest
    | .default_ ss :: rest => checkStmts true ss && checkSwitchCases rest
end

/-
noFreeVars : TyEnv → CppExpr → Bool

式に未束縛の変数が現れないことを確認。
-/
def noFreeVarsExpr (Γ : TyEnv) : CppExpr → Bool
  | .lit _            => true
  | .var x            => Γ.lookup x |>.isSome
  | .binop _ e1 e2    => noFreeVarsExpr Γ e1 && noFreeVarsExpr Γ e2
  | .unop _ e         => noFreeVarsExpr Γ e
  | .assign _ e1 e2   => noFreeVarsExpr Γ e1 && noFreeVarsExpr Γ e2
  | .call f args      =>
      noFreeVarsExpr Γ f &&
      args.all (noFreeVarsExpr Γ)
  | .member e _       => noFreeVarsExpr Γ e
  | .arrow e _        => noFreeVarsExpr Γ e
  | .index e1 e2      => noFreeVarsExpr Γ e1 && noFreeVarsExpr Γ e2
  | .addrOf e         => noFreeVarsExpr Γ e
  | .deref e          => noFreeVarsExpr Γ e
  | .ternary c e1 e2  =>
      noFreeVarsExpr Γ c &&
      noFreeVarsExpr Γ e1 &&
      noFreeVarsExpr Γ e2
  | .cast _ e         => noFreeVarsExpr Γ e
  | .sizeofExpr e     => noFreeVarsExpr Γ e
  | .sizeofType _     => true
  | .new_ _ (some e)  => noFreeVarsExpr Γ e
  | .new_ _ none      => true
  | .delete_ e        => noFreeVarsExpr Γ e
  | .comma e1 e2      => noFreeVarsExpr Γ e1 && noFreeVarsExpr Γ e2

end WellFormedness

-- ============================================================
-- §C. 型付け判断
-- ============================================================

section Typing

/-
HasType : TyEnv → CppExpr → CppType → Prop

型判断 Γ ⊢ e : τ の形式化。
big-step 意味論の前に、構文レベルで型を決定する。

ここでは核断片（Phase 3 の参照意味論の対象）を優先する：
  lit, var, addrOf, deref, assign, binop（算術・比較）
  unop, ternary, call, member, arrow, index
-/

-- 二項演算の型規則
-- 算術演算と比較演算を分ける
def BinOp.isArith : BinOp → Bool
  | .add | .sub | .mul | .div | .mod => true
  | _ => false

def BinOp.isCompare : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def BinOp.isLogic : BinOp → Bool
  | .and | .or => true
  | _ => false

def BinOp.isBitwise : BinOp → Bool
  | .bitAnd | .bitOr | .bitXor | .shl | .shr => true
  | _ => false

-- StructTable から named 型のフィールドの型を引く
def StructTable.fieldType (st : StructTable) (name field : Ident) : Option CppType :=
  match st.lookup name with
  | none => none
  | some members =>
      members.findSome? fun m =>
        match m with
        | .field τ fname _ => if fname == field then some τ else none
        | _ => none

/-
型判断の本体。
StructTable を受け取るのは、named 型のフィールドアクセスに必要なため。
-/
inductive HasType (Γ : TyEnv) (st : StructTable) : CppExpr → CppType → Prop where

  -- リテラル
  | T_LitInt : ∀ (n : Int),
      HasType Γ st (.lit (.int n)) CInt

  | T_LitUInt : ∀ (n : Nat),
      HasType Γ st (.lit (.uint n)) CUInt

  | T_LitFloat : ∀ (x : Float),
      HasType Γ st (.lit (.float x)) CFloat

  | T_LitDouble : ∀ (x : Float),
      HasType Γ st (.lit (.double x)) CDouble

  | T_LitBool : ∀ (b : Bool),
      HasType Γ st (.lit (.bool b)) CBool

  | T_LitNull : ∀ (τ : CppType),
      HasType Γ st (.lit .null) (.ptr τ)

  -- 変数
  | T_Var : ∀ (x : Ident) (τ : CppType),
      Γ.lookup x = some τ →
      HasType Γ st (.var x) τ

  -- 算術二項演算（int × int → int）
  | T_BinArithInt : ∀ (op : BinOp) (e1 e2 : CppExpr),
      op.isArith = true →
      HasType Γ st e1 CInt →
      HasType Γ st e2 CInt →
      HasType Γ st (.binop op e1 e2) CInt

  -- 算術二項演算（float × float → float）
  | T_BinArithFloat : ∀ (op : BinOp) (e1 e2 : CppExpr),
      op.isArith = true →
      HasType Γ st e1 CFloat →
      HasType Γ st e2 CFloat →
      HasType Γ st (.binop op e1 e2) CFloat

  -- 比較演算（τ × τ → bool）
  | T_BinCompare : ∀ (op : BinOp) (e1 e2 : CppExpr) (τ : CppType),
      op.isCompare = true →
      HasType Γ st e1 τ →
      HasType Γ st e2 τ →
      HasType Γ st (.binop op e1 e2) CBool

  -- 論理演算（bool × bool → bool）
  | T_BinLogic : ∀ (op : BinOp) (e1 e2 : CppExpr),
      op.isLogic = true →
      HasType Γ st e1 CBool →
      HasType Γ st e2 CBool →
      HasType Γ st (.binop op e1 e2) CBool

  -- 単項否定
  | T_UnNeg : ∀ (e : CppExpr),
      HasType Γ st e CInt →
      HasType Γ st (.unop .neg e) CInt

  | T_UnNot : ∀ (e : CppExpr),
      HasType Γ st e CBool →
      HasType Γ st (.unop .not e) CBool

  -- インクリメント/デクリメント（代入可能な int 式のみ）
  | T_PreInc : ∀ (e : CppExpr),
      isAssignable e →
      HasType Γ st e CInt →
      HasType Γ st (.unop .preinc e) CInt

  | T_PreDec : ∀ (e : CppExpr),
      isAssignable e →
      HasType Γ st e CInt →
      HasType Γ st (.unop .predec e) CInt

  | T_PostInc : ∀ (e : CppExpr),
      isAssignable e →
      HasType Γ st e CInt →
      HasType Γ st (.unop .postinc e) CInt

  | T_PostDec : ∀ (e : CppExpr),
      isAssignable e →
      HasType Γ st e CInt →
      HasType Γ st (.unop .postdec e) CInt

  -- アドレス取得  &e : τ*
  | T_AddrOf : ∀ (e : CppExpr) (τ : CppType),
      isAssignable e →      -- &e は lvalue にしか適用できない
      HasType Γ st e τ →
      HasType Γ st (.addrOf e) (.ptr τ)

  -- デリファレンス  *e : τ  （e : τ*）
  -- NoUB 仮定下では e がヌルポインタでないことを前提にする
  | T_Deref : ∀ (e : CppExpr) (τ : CppType),
      HasType Γ st e (.ptr τ) →
      HasType Γ st (.deref e) τ

  -- 代入  e1 = e2 : τ
  | T_Assign : ∀ (e1 e2 : CppExpr) (τ : CppType),
      isAssignable e1 →     -- 左辺は代入可能
      HasType Γ st e1 τ →
      HasType Γ st e2 τ →
      HasType Γ st (.assign .assign e1 e2) τ

  -- 複合代入  e1 += e2 : int
  | T_AddAssign : ∀ (e1 e2 : CppExpr),
      isAssignable e1 →
      HasType Γ st e1 CInt →
      HasType Γ st e2 CInt →
      HasType Γ st (.assign .addAssign e1 e2) CInt

  | T_SubAssign : ∀ (e1 e2 : CppExpr),
      isAssignable e1 →
      HasType Γ st e1 CInt →
      HasType Γ st e2 CInt →
      HasType Γ st (.assign .subAssign e1 e2) CInt

  -- 三項演算子  c ? e1 : e2 : τ
  | T_Ternary : ∀ (c e1 e2 : CppExpr) (τ : CppType),
      HasType Γ st c CBool →
      HasType Γ st e1 τ →
      HasType Γ st e2 τ →
      HasType Γ st (.ternary c e1 e2) τ

  -- 関数呼び出し  f(args) : τ_ret
  | T_Call : ∀ (f : CppExpr) (args : List CppExpr)
               (paramTys : List CppType) (retTy : CppType),
      HasType Γ st f (.func paramTys retTy) →
      args.length = paramTys.length →
      (∀ i (hi : i < args.length),
        HasType Γ st args[i] paramTys[i]'(by omega)) →
      HasType Γ st (.call f args) retTy

  -- メンバアクセス  e.field : τ_field
  | T_Member : ∀ (e : CppExpr) (name field : Ident) (τ_field : CppType),
      HasType Γ st e (.named name) →
      st.fieldType name field = some τ_field →
      HasType Γ st (.member e field) τ_field

  -- ポインタメンバ  e->field : τ_field
  | T_Arrow : ∀ (e : CppExpr) (name field : Ident) (τ_field : CppType),
      HasType Γ st e (.ptr (.named name)) →
      st.fieldType name field = some τ_field →
      HasType Γ st (.arrow e field) τ_field

  -- 配列添字  e1[e2] : τ_elem
  | T_Index : ∀ (e1 e2 : CppExpr) (τ_elem : CppType) (n : Nat),
      HasType Γ st e1 (.array τ_elem n) →
      HasType Γ st e2 CInt →
      HasType Γ st (.index e1 e2) τ_elem

  -- キャスト（核断片では static_cast のみ、安全なものに限る）
  | T_CastIntToFloat : ∀ (e : CppExpr),
      HasType Γ st e CInt →
      HasType Γ st (.cast CFloat e) CFloat

  | T_CastFloatToInt : ∀ (e : CppExpr),
      HasType Γ st e CFloat →
      HasType Γ st (.cast CInt e) CInt

  | T_CastIntToBool : ∀ (e : CppExpr),
      HasType Γ st e CInt →
      HasType Γ st (.cast CBool e) CBool

  -- sizeof は常に uint を返す
  | T_SizeofType : ∀ (τ : CppType),
      HasType Γ st (.sizeofType τ) CUInt

  | T_SizeofExpr : ∀ (e : CppExpr) (τ : CppType),
      HasType Γ st e τ →
      HasType Γ st (.sizeofExpr e) CUInt

  -- new : τ*
  | T_New : ∀ (τ : CppType) (initOpt : Option CppExpr),
      (∀ e, initOpt = some e → HasType Γ st e τ) →
      HasType Γ st (.new_ τ initOpt) (.ptr τ)

  -- delete : void
  | T_Delete : ∀ (e : CppExpr) (τ : CppType),
      HasType Γ st e (.ptr τ) →
      HasType Γ st (.delete_ e) CVoid

  -- コンマ演算子: 右辺の型
  | T_Comma : ∀ (e1 e2 : CppExpr) (τ1 τ2 : CppType),
      HasType Γ st e1 τ1 →
      HasType Γ st e2 τ2 →
      HasType Γ st (.comma e1 e2) τ2

/-
文の型付け判断。
return の型チェックのために「期待される戻り値型」retTy を渡す。
-/
inductive HasTypeStmt
    (Γ : TyEnv) (st : StructTable) (retTy : CppType)
    : CppStmt → Prop where

  | T_Skip :
      HasTypeStmt Γ st retTy .skip

  | T_Expr : ∀ (e : CppExpr) (τ : CppType),
      HasType Γ st e τ →
      HasTypeStmt Γ st retTy (.expr e)

  | T_Block : ∀ (ss : List CppStmt),
      (∀ s ∈ ss, HasTypeStmt Γ st retTy s) →
      HasTypeStmt Γ st retTy (.block ss)

  | T_Decl : ∀ (d : VarDecl),
      -- 初期化式がある場合は型整合を確認
      (∀ e, d.init = .direct e → HasType Γ st e d.type) →
      HasTypeStmt Γ st retTy (.decl d)

  | T_Ite : ∀ (c : CppExpr) (s1 s2 : CppStmt),
      HasType Γ st c CBool →
      HasTypeStmt Γ st retTy s1 →
      HasTypeStmt Γ st retTy s2 →
      HasTypeStmt Γ st retTy (.ite c s1 s2)

  | T_While : ∀ (c : CppExpr) (body : CppStmt),
      HasType Γ st c CBool →
      HasTypeStmt Γ st retTy body →
      HasTypeStmt Γ st retTy (.while_ c body)

  | T_DoWhile : ∀ (body : CppStmt) (c : CppExpr),
      HasTypeStmt Γ st retTy body →
      HasType Γ st c CBool →
      HasTypeStmt Γ st retTy (.doWhile body c)

  | T_For : ∀ (init : ForInit) (cond step : Option CppExpr) (body : CppStmt),
      (∀ e, cond = some e → HasType Γ st e CBool) →
      HasTypeStmt Γ st retTy body →
      HasTypeStmt Γ st retTy (.for_ init cond step body)

  | T_ReturnVoid :
      retTy = CVoid →
      HasTypeStmt Γ st retTy (.return_ none)

  | T_ReturnValue : ∀ (e : CppExpr),
      HasType Γ st e retTy →
      HasTypeStmt Γ st retTy (.return_ (some e))

  | T_Break :
      HasTypeStmt Γ st retTy .break_

  | T_Continue :
      HasTypeStmt Γ st retTy .continue_

  | T_Switch : ∀ (e : CppExpr) (cases : List SwitchCase),
      HasType Γ st e CInt →
      HasTypeStmt Γ st retTy (.switch_ e cases)

end Typing

-- ============================================================
-- §D. State の型整合
-- ============================================================

section StateTyping

/-
StoreWellTyped : Store → Prop

store の全 cell が CellWellTyped を満たすこと。
これが Phase 5 の「typed-state preservation」の基盤。
-/
def StoreWellTyped (store : Store) : Prop :=
  ∀ l c, Store.read store l = some c → CellWellTyped c

/-
TypedState : TyEnv → State → Prop

実行状態 s が型環境 Γ と整合していること。
具体的には：
  1. Γ に登録された変数 x の型 τ について
     s.locOf x が存在し、その場所が τ 型の cell を持つ
  2. store 全体が well-typed
-/
def TypedState (Γ : TyEnv) (s : State) : Prop :=
  StoreWellTyped s.store ∧
  ∀ x τ, Γ.lookup x = some τ →
    ∃ l, s.locOf x = some l ∧ LValueHasType s l τ

/-
TypedFunc : FuncTable → TyEnv → StructTable → Prop

関数テーブル内の全関数が型付けされていること。
-/
def TypedFunc (ft : FuncTable) (Γ : TyEnv) (structs : StructTable) : Prop :=
  ∀ name fd, FuncTable.lookup ft name = some fd →
    let paramTys := fd.params.map (·.type)
    let paramBindings := fd.params.map (fun p => (p.name, p.type))
    let Γ' := Γ.extendMany paramBindings
    HasTypeStmt Γ' structs fd.returnType fd.body

end StateTyping

-- ============================================================
-- §E. 型付けの基本補題（Phase 5 の preservation の部品）
-- ============================================================

section TypingLemmas

-- RValueHasType の一意性（型は一意に決まる）
-- ただし ptr τ1 と ptr τ2 は同じ ptr 値を持てるので「型が一意」ではない
-- ここでは「型タグが一意」を示す
theorem rvalueHasType_tag_consistent :
    ∀ (v : RValue) (τ1 τ2 : CppType),
    RValueHasType v τ1 → RValueHasType v τ2 →
    v.tag = (.int : ValueTag) → τ1 = CInt → τ2 = CInt := by
  intro v τ1 τ2 h1 h2 htag hτ1
  cases h1 with
  | int n => cases h2 with | int _ => exact hτ1 ▸ rfl

-- void rvalue は void 型のみ
theorem void_has_only_void_type (τ : CppType) :
    RValueHasType .void τ → τ = CVoid := by
  intro h
  cases h
  rfl

-- bool rvalue は bool 型のみ
theorem bool_has_only_bool_type (b : Bool) (τ : CppType) :
    RValueHasType (.bool b) τ → τ = CBool := by
  intro h
  cases h
  rfl

-- ObjectFitsType と isAssignable の関係
-- スカラ型のオブジェクトは スカラの型（配列型でも named 型でもない）
theorem scalar_fits_non_aggregate :
    ∀ (v : RValue) (τ : CppType),
    ObjectFitsType (.scalar v) τ →
    ∃ τ', RValueHasType v τ' ∧ τ = τ' := by
  intro v τ h
  cases h with
  | scalar v' τ' hv => exact ⟨τ', hv, rfl⟩

-- CellWellTyped の write 安定性
-- 同じ型で overwrite すると CellWellTyped が保たれる
theorem cellWellTyped_overwriteScalar :
    ∀ (c : Cell) (v : RValue),
    CellWellTyped c →
    RValueHasType v c.ty →
    CellWellTyped (c.overwriteScalar v) := by
  intro c v hc hv
  simp [CellWellTyped, Cell.overwriteScalar]
  exact ObjectFitsType.scalar v c.ty hv

-- StoreWellTyped は write で保たれる（型が一致するなら）
theorem storeWellTyped_write :
    ∀ (store : Store) (l : Loc) (c_old c_new : Cell),
    StoreWellTyped store →
    Store.read store l = some c_old →
    c_new.ty = c_old.ty →
    CellWellTyped c_new →
    StoreWellTyped (Store.write store l c_new) := by
  intro store l c_old c_new hWT hread hty hcell
  intro l' c' hread'
  by_cases h : l' = l
  · subst h
    rw [Store.read_write_eq] at hread'
    cases hread'
    exact hcell
  · -- l' ≠ l の場合: write は l' の cell に影響しない
    sorry -- Phase 5 で Store.read_write_ne を使って証明

end TypingLemmas

-- ============================================================
-- §F. 使用例（サニティチェック）
-- ============================================================

section Examples

-- RValueHasType の例
example : RValueHasType (.int 42) CInt :=
  RValueHasType.int 42

example : RValueHasType (.bool true) CBool :=
  RValueHasType.bool true

example : RValueHasType (.ptr nullLoc) (.ptr CInt) :=
  RValueHasType.ptrNull CInt

-- ObjectFitsType の例
example : ObjectFitsType (.scalar (.int 0)) CInt :=
  ObjectFitsType.scalar (.int 0) CInt (RValueHasType.int 0)

-- CellWellTyped の例
def exCell : Cell :=
  { ty := CInt, object := .scalar (.int 42),
    storage := .stack, initialized := true, alive := true }

example : CellWellTyped exCell :=
  ObjectFitsType.scalar (.int 42) CInt (RValueHasType.int 42)

-- HasType の例: Γ ⊢ (x + 1) : int  (x : int ∈ Γ)
example :
    let Γ : TyEnv := [("x", CInt)]
    HasType Γ [] (.binop .add (.var "x") (.lit (.int 1))) CInt := by
  apply HasType.T_BinArithInt
  · rfl
  · exact HasType.T_Var "x" CInt rfl
  · exact HasType.T_LitInt 1

-- isAssignable の例
example : isAssignable (.var "x") := trivial
example : ¬ isAssignable (.lit (.int 42)) := id

-- HasType でキャプチャした代入: Γ ⊢ (x = 42) : int
example :
    let Γ : TyEnv := [("x", CInt)]
    HasType Γ [] (.assign .assign (.var "x") (.lit (.int 42))) CInt := by
  apply HasType.T_Assign
  · exact trivial   -- isAssignable (.var "x")
  · exact HasType.T_Var "x" CInt rfl
  · exact HasType.T_LitInt 42

end Examples

end Cpp
