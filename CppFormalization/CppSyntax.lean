-- ============================================================
-- C++ Syntax Formalization in Lean4
-- Phase 1: Syntax (Inductive Types)
--
-- 設計方針：
--   - UBは一切起きないという仮定を前提とする
--   - 理想化度により「モデル化しない要素」を明示的に除外
--   - 各定義にはISO C++規格の対応箇所をコメントで明記
-- ============================================================

namespace Cpp

-- ============================================================
-- §1. 基本識別子・リテラル
-- ============================================================

-- 変数名・関数名の識別子
abbrev Ident := String

-- C++の基本型 [ISO C++ §6.8]
inductive BaseType : Type where
  | void                          -- void
  | bool                          -- bool
  | char                          -- char
  | int                           -- int  (理想化: 数学的整数 ℤ として扱う)
  | uint                          -- unsigned int
  | float                         -- float  (理想化: 実数 ℝ として扱う)
  | double                        -- double
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- §2. 型システム [ISO C++ §6]
-- ============================================================

-- C++の型
-- 理想化: テンプレート型・CV修飾子(const/volatile)は Phase 4 以降で扱う
inductive CppType : Type where
  -- 基本型
  | base    : BaseType → CppType

  -- ポインタ型  T*
  -- 理想化: メモリアドレスを抽象化（NoUB仮定下では安全）
  | ptr     : CppType → CppType

  -- 参照型  T&
  -- 理想化: ポインタの糖衣構文として扱う
  | ref     : CppType → CppType

  -- 配列型  T[n]
  -- 理想化: 長さを型レベルで保持（範囲外アクセスはUBなので除外済み）
  | array   : CppType → Nat → CppType

  -- 関数型  (T1, T2, ...) → R
  | func    : List CppType → CppType → CppType

  -- struct / class 型（名前で参照）
  | named   : Ident → CppType

  deriving Repr, BEq

private theorem lt_add_extra (n k : Nat) : n < n + (k + 1) :=
  Nat.lt_of_lt_of_le
    (Nat.lt_succ_self n)
    (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) n)

private theorem lt_size_step (n k : Nat) : n < n + 1 + k := by
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
  simp [Nat.add_left_comm, Nat.add_comm]


mutual
  private def cppTypeDecEq : (a b : CppType) → Decidable (a = b)
    | CppType.base t₁, CppType.base t₂ =>
        match decEq t₁ t₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | CppType.ptr t₁, CppType.ptr t₂ =>
        match cppTypeDecEq t₁ t₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | CppType.ref t₁, CppType.ref t₂ =>
        match cppTypeDecEq t₁ t₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | CppType.array t₁ n₁, CppType.array t₂ n₂ =>
        match cppTypeDecEq t₁ t₂, decEq n₁ n₂ with
        | isTrue h₁, isTrue h₂ => isTrue (by cases h₁; cases h₂; rfl)
        | isFalse h₁, _ => isFalse (by intro hEq; cases hEq; exact h₁ rfl)
        | _, isFalse h₂ => isFalse (by intro hEq; cases hEq; exact h₂ rfl)
    | CppType.func as₁ r₁, CppType.func as₂ r₂ =>
        match cppTypeListDecEq as₁ as₂, cppTypeDecEq r₁ r₂ with
        | isTrue h₁, isTrue h₂ => isTrue (by cases h₁; cases h₂; rfl)
        | isFalse h₁, _ => isFalse (by intro hEq; cases hEq; exact h₁ rfl)
        | _, isFalse h₂ => isFalse (by intro hEq; cases hEq; exact h₂ rfl)
    | CppType.named n₁, CppType.named n₂ =>
        match decEq n₁ n₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | CppType.base _, CppType.ptr _      => isFalse (by intro h; cases h)
    | CppType.base _, CppType.ref _      => isFalse (by intro h; cases h)
    | CppType.base _, CppType.array _ _  => isFalse (by intro h; cases h)
    | CppType.base _, CppType.func _ _   => isFalse (by intro h; cases h)
    | CppType.base _, CppType.named _    => isFalse (by intro h; cases h)
    | CppType.ptr _, CppType.base _      => isFalse (by intro h; cases h)
    | CppType.ptr _, CppType.ref _       => isFalse (by intro h; cases h)
    | CppType.ptr _, CppType.array _ _   => isFalse (by intro h; cases h)
    | CppType.ptr _, CppType.func _ _    => isFalse (by intro h; cases h)
    | CppType.ptr _, CppType.named _     => isFalse (by intro h; cases h)
    | CppType.ref _, CppType.base _      => isFalse (by intro h; cases h)
    | CppType.ref _, CppType.ptr _       => isFalse (by intro h; cases h)
    | CppType.ref _, CppType.array _ _   => isFalse (by intro h; cases h)
    | CppType.ref _, CppType.func _ _    => isFalse (by intro h; cases h)
    | CppType.ref _, CppType.named _     => isFalse (by intro h; cases h)
    | CppType.array _ _, CppType.base _  => isFalse (by intro h; cases h)
    | CppType.array _ _, CppType.ptr _   => isFalse (by intro h; cases h)
    | CppType.array _ _, CppType.ref _   => isFalse (by intro h; cases h)
    | CppType.array _ _, CppType.func _ _ => isFalse (by intro h; cases h)
    | CppType.array _ _, CppType.named _ => isFalse (by intro h; cases h)
    | CppType.func _ _, CppType.base _   => isFalse (by intro h; cases h)
    | CppType.func _ _, CppType.ptr _    => isFalse (by intro h; cases h)
    | CppType.func _ _, CppType.ref _    => isFalse (by intro h; cases h)
    | CppType.func _ _, CppType.array _ _ => isFalse (by intro h; cases h)
    | CppType.func _ _, CppType.named _  => isFalse (by intro h; cases h)
    | CppType.named _, CppType.base _    => isFalse (by intro h; cases h)
    | CppType.named _, CppType.ptr _     => isFalse (by intro h; cases h)
    | CppType.named _, CppType.ref _     => isFalse (by intro h; cases h)
    | CppType.named _, CppType.array _ _ => isFalse (by intro h; cases h)
    | CppType.named _, CppType.func _ _  => isFalse (by intro h; cases h)
    termination_by a b => sizeOf a + sizeOf b
  decreasing_by
    all_goals simp_wf
    -- ptr: sizeOf t₁ + sizeOf t₂ < (1 + sizeOf t₁) + (1 + sizeOf t₂)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      lt_size_step (sizeOf t₁ + sizeOf t₂) 1
    -- ref: 同上
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      lt_size_step (sizeOf t₁ + sizeOf t₂) 1
    -- array: sizeOf t₁ + sizeOf t₂ < (1 + sizeOf t₁ + n₁) + (1 + sizeOf t₂ + n₂)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      lt_size_step (sizeOf t₁ + sizeOf t₂) (n₁ + n₂ + 1)
    -- func (リスト側): sizeOf as₁ + sizeOf as₂ < (1 + sizeOf as₁ + sizeOf r₁) + (1 + sizeOf as₂ + sizeOf r₂)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        lt_add_extra (sizeOf as₁ + sizeOf as₂) (sizeOf r₁ + sizeOf r₂ + 1)
    -- func (戻り値側)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        lt_add_extra (sizeOf r₁ + sizeOf r₂) (sizeOf as₁ + sizeOf as₂ + 1)


  private def cppTypeListDecEq : (xs ys : List CppType) → Decidable (xs = ys)
    | [], []         => isTrue rfl
    | [], _ :: _     => isFalse (by intro h; cases h)
    | _ :: _, []     => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match cppTypeDecEq x y, cppTypeListDecEq xs ys with
        | isTrue h₁,  isTrue h₂  => isTrue (by cases h₁; cases h₂; rfl)
        | isFalse h₁, _          => isFalse (by intro hEq; cases hEq; exact h₁ rfl)
        | _,          isFalse h₂ => isFalse (by intro hEq; cases hEq; exact h₂ rfl)
  termination_by xs ys => sizeOf xs + sizeOf ys
  decreasing_by
    all_goals simp_wf
    -- x :: xs, y :: ys → cppTypeDecEq x y の呼び出し
    -- sizeOf x + sizeOf y < (1 + sizeOf x + sizeOf xs) + (1 + sizeOf y + sizeOf ys)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        lt_add_extra (sizeOf x + sizeOf y) (sizeOf xs + sizeOf ys + 1)
    -- x :: xs, y :: ys → cppTypeListDecEq xs ys の呼び出し
    -- sizeOf xs + sizeOf ys < (1 + sizeOf x + sizeOf xs) + (1 + sizeOf y + sizeOf ys)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        lt_add_extra (sizeOf xs + sizeOf ys) (sizeOf x + sizeOf y + 1)
end

instance : DecidableEq CppType := cppTypeDecEq

-- 型の略記
notation "CVoid"   => CppType.base BaseType.void
notation "CBool"   => CppType.base BaseType.bool
notation "CInt"    => CppType.base BaseType.int
notation "CUInt"   => CppType.base BaseType.uint
notation "CFloat"  => CppType.base BaseType.float
notation "CDouble" => CppType.base BaseType.double

-- ============================================================
-- §3. リテラル値 [ISO C++ §5.13]
-- ============================================================

inductive Literal : Type where
  | int    : Int    → Literal   -- 整数リテラル  42, -1, 0
  | uint   : Nat    → Literal   -- 符号なし整数  42u
  | float  : Float  → Literal   -- 浮動小数点   3.14f
  | double : Float  → Literal   -- 倍精度       3.14
  | bool   : Bool   → Literal   -- true / false
  | char   : Char   → Literal   -- 'a'
  | null   : Literal             -- nullptr
  deriving Repr, BEq

-- ============================================================
-- §4. 演算子 [ISO C++ §7]
-- ============================================================

-- 二項演算子
inductive BinOp : Type where
  -- 算術 [§7.6.5 - §7.6.8]
  | add | sub | mul | div | mod
  -- 比較 [§7.6.9 - §7.6.10]
  | eq | ne | lt | le | gt | ge
  -- 論理 [§7.6.14 - §7.6.15]
  | and | or
  -- ビット演算 [§7.6.11 - §7.6.13]
  | bitAnd | bitOr | bitXor | shl | shr
  deriving Repr, DecidableEq, BEq

-- 単項演算子
inductive UnOp : Type where
  | neg    -- 算術否定   -e
  | not    -- 論理否定   !e
  | bitNot -- ビット否定 ~e
  | preinc -- 前置インクリメント  ++e
  | predec -- 前置デクリメント   --e
  | postinc -- 後置インクリメント e++
  | postdec -- 後置デクリメント  e--
  deriving Repr, DecidableEq, BEq

-- 代入演算子（複合代入を含む）
inductive AssignOp : Type where
  | assign                        -- =
  | addAssign | subAssign         -- += -=
  | mulAssign | divAssign         -- *= /=
  | modAssign                     -- %=
  | shlAssign | shrAssign         -- <<= >>=
  | bitAndAssign | bitOrAssign    -- &= |=
  | bitXorAssign                  -- ^=
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- §5. 式 (Expression) [ISO C++ §7]
-- ============================================================

-- 相互再帰定義：式と初期化子が互いを参照する
inductive CppExpr : Type where

  -- リテラル [§5.13]
  | lit      : Literal → CppExpr

  -- 変数参照 [§7.5.4]
  | var      : Ident → CppExpr

  -- 二項演算 [§7.6]
  | binop    : BinOp → CppExpr → CppExpr → CppExpr

  -- 単項演算 [§7.6]
  | unop     : UnOp → CppExpr → CppExpr

  -- 代入式 [§7.6.19]
  | assign   : AssignOp → CppExpr → CppExpr → CppExpr

  -- 関数呼び出し [§7.6.1.3]
  | call     : CppExpr → List CppExpr → CppExpr

  -- メンバアクセス  e.field  [§7.6.1.5]
  | member   : CppExpr → Ident → CppExpr

  -- ポインタメンバアクセス  e->field  [§7.6.1.6]
  -- 理想化: NoUB仮定下では e ≠ nullptr が保証される
  | arrow    : CppExpr → Ident → CppExpr

  -- 添字アクセス  e1[e2]  [§7.6.1.2]
  -- 理想化: NoUB仮定下では範囲内アクセスが保証される
  | index    : CppExpr → CppExpr → CppExpr

  -- アドレス取得  &e  [§7.6.2.4]
  | addrOf   : CppExpr → CppExpr

  -- 間接参照（デリファレンス）  *e  [§7.6.2.3]
  -- 理想化: NoUB仮定下ではヌルポインタ参照は起きない
  | deref    : CppExpr → CppExpr

  -- 三項演算子  cond ? e1 : e2  [§7.6.16]
  | ternary  : CppExpr → CppExpr → CppExpr → CppExpr

  -- キャスト  static_cast<T>(e)  [§7.6.1.9]
  -- 理想化: 有効なキャストのみ（NoUB仮定で不正キャストは除外）
  | cast     : CppType → CppExpr → CppExpr

  -- sizeof  [§7.6.2.6]
  -- 理想化: コンパイル時定数として扱う
  | sizeofExpr : CppExpr → CppExpr
  | sizeofType : CppType → CppExpr

  -- new / delete  [§7.6.2.7, §7.6.2.9]
  -- 理想化: メモリ確保は必ず成功する（NoUB仮定の帰結）
  | new_     : CppType → Option CppExpr → CppExpr
  | delete_  : CppExpr → CppExpr

  -- コンマ演算子  e1, e2  [§7.6.20]
  | comma    : CppExpr → CppExpr → CppExpr

  deriving Repr, BEq

-- ============================================================
-- §6. 文 (Statement) [ISO C++ §8]
-- ============================================================

-- 変数宣言の初期化子
inductive Initializer : Type where
  | direct : CppExpr → Initializer         -- int x = e; または int x(e);
  | list   : List CppExpr → Initializer    -- int x{e1, e2};
  | none   : Initializer                   -- int x;（未初期化）
  -- 理想化: §4 の uninitRead UBがあるため
  --         none の場合は NoUB仮定下では読まないことを別途証明が必要
  deriving Repr, BEq

-- ローカル変数宣言
structure VarDecl : Type where
  type  : CppType
  name  : Ident
  init  : Initializer
  deriving Repr, BEq

mutual

  -- 文
  inductive CppStmt : Type where

    -- 空文  ;  [§8.1]
    | skip : CppStmt

    -- 式文  e;  [§8.2]
    | expr : CppExpr → CppStmt

    -- ブロック  { s1; s2; ... }  [§8.3]
    | block : List CppStmt → CppStmt

    -- ローカル変数宣言文  T x = e;  [§8.4]
    | decl : VarDecl → CppStmt

    -- if文  [§8.5.1]
    | ite : CppExpr → CppStmt → CppStmt → CppStmt

    -- while文  [§8.6.1]
    | while_ : CppExpr → CppStmt → CppStmt

    -- for文  for(init; cond; step) body  [§8.6.4]
    | for_ : ForInit → Option CppExpr → Option CppExpr → CppStmt → CppStmt

    -- range-based for  for(T x : e) body  [§8.6.5]
    | forRange : CppType → Ident → CppExpr → CppStmt → CppStmt

    -- return文  [§8.7.3]
    | return_ : Option CppExpr → CppStmt

    -- break / continue  [§8.7.1, §8.7.2]
    | break_ : CppStmt
    | continue_ : CppStmt

    -- switch文  [§8.5.2]
    | switch_ : CppExpr → List SwitchCase → CppStmt

    -- do-while文  [§8.6.2]
    | doWhile : CppStmt → CppExpr → CppStmt

    deriving Repr, BEq

  -- for文の初期化部分（宣言 or 式）
  inductive ForInit : Type where
    | decl : VarDecl  → ForInit
    | expr : CppExpr  → ForInit
    | none : ForInit
    deriving Repr, BEq

  -- switch文のケース
  inductive SwitchCase : Type where
    | case_    : Literal → List CppStmt → SwitchCase   -- case x:
    | default_ : List CppStmt → SwitchCase              -- default:
    deriving Repr, BEq

end

-- ============================================================
-- §7. 宣言・定義 (Declaration) [ISO C++ §9]
-- ============================================================

-- 関数パラメータ
structure Param : Type where
  type    : CppType
  name    : Ident
  default : Option CppExpr  -- デフォルト引数
  deriving Repr, BEq

-- 関数定義 [ISO C++ §9.5]
structure FuncDef : Type where
  returnType : CppType
  name       : Ident
  params     : List Param
  body       : CppStmt      -- block が想定される
  deriving Repr, BEq

-- struct / class のメンバ [ISO C++ §11]
inductive MemberDecl : Type where
  | field  : CppType → Ident → Option CppExpr → MemberDecl  -- フィールド
  | method : FuncDef → MemberDecl                             -- メソッド
  | ctor   : List Param → CppStmt → MemberDecl               -- コンストラクタ
  | dtor   : CppStmt → MemberDecl                             -- デストラクタ
  deriving Repr, BEq

-- struct / class 定義 [ISO C++ §11]
structure StructDef : Type where
  name    : Ident
  members : List MemberDecl
  deriving Repr, BEq

-- トップレベル宣言
inductive TopDecl : Type where
  | func      : FuncDef → TopDecl                       -- 関数定義
  | struct_   : StructDef → TopDecl                     -- struct定義
  | globalVar : VarDecl → TopDecl                       -- グローバル変数
  | typeAlias : Ident → CppType → TopDecl               -- using T = ...
  deriving Repr, BEq

-- ============================================================
-- §8. プログラム全体
-- ============================================================

-- 翻訳単位（= 1つの .cpp ファイルのモデル）
structure CppProgram : Type where
  decls : List TopDecl
  -- エントリーポイントは "main" という名前の FuncDef と約束する
  deriving Repr, BEq

-- ============================================================
-- §9. 構文上の補題（Phase 2 以降の準備）
-- ============================================================

mutual

  -- 式リストの深さ
  def exprListDepth : List CppExpr → Nat
    | []      => 0
    | e :: es => max e.depth (exprListDepth es)

  -- 初期化子の深さ
  def Initializer.depth : Initializer → Nat
    | .direct e => e.depth
    | .list es  => exprListDepth es
    | .none     => 0

  -- 式の深さ（停止性証明のための測度）
  def CppExpr.depth : CppExpr → Nat
    | .lit _            => 1
    | .var _            => 1
    | .binop _ e1 e2    => 1 + max e1.depth e2.depth
    | .unop _ e         => 1 + e.depth
    | .assign _ e1 e2   => 1 + max e1.depth e2.depth
    | .call f args      => 1 + max f.depth (exprListDepth args)
    | .member e _       => 1 + e.depth
    | .arrow e _        => 1 + e.depth
    | .index e1 e2      => 1 + max e1.depth e2.depth
    | .addrOf e         => 1 + e.depth
    | .deref e          => 1 + e.depth
    | .ternary c e1 e2  => 1 + max c.depth (max e1.depth e2.depth)
    | .cast _ e         => 1 + e.depth
    | .sizeofExpr e     => 1 + e.depth
    | .sizeofType _     => 1
    | .new_ _ (some e)  => 1 + e.depth
    | .new_ _ none      => 1
    | .delete_ e        => 1 + e.depth
    | .comma e1 e2      => 1 + max e1.depth e2.depth

  -- 変数宣言の深さ
  def VarDecl.depth : VarDecl → Nat
    | ⟨_, _, init⟩ => 1 + init.depth

  -- for 初期化部の深さ
  def ForInit.depth : ForInit → Nat
    | .decl d => d.depth
    | .expr e => e.depth
    | .none   => 0

  -- 文リストの深さ
  def stmtListDepth : List CppStmt → Nat
    | []      => 0
    | s :: ss => max s.depth (stmtListDepth ss)

  -- switch case の深さ
  def SwitchCase.depth : SwitchCase → Nat
    | .case_ _ ss   => stmtListDepth ss
    | .default_ ss  => stmtListDepth ss

  -- switch case リストの深さ
  def switchCaseListDepth : List SwitchCase → Nat
    | []      => 0
    | c :: cs => max c.depth (switchCaseListDepth cs)

  -- 文の深さ
  def CppStmt.depth : CppStmt → Nat
    | .skip             => 1
    | .expr e           => 1 + e.depth
    | .block ss         => 1 + stmtListDepth ss
    | .decl d           => 1 + d.depth
    | .ite c s1 s2      => 1 + max c.depth (max s1.depth s2.depth)
    | .while_ c s       => 1 + max c.depth s.depth
    | .for_ init cond step s =>
        1 + max init.depth
          (max
            (match cond with
             | none   => 0
             | some e => e.depth)
            (max
              (match step with
               | none   => 0
               | some e => e.depth)
              s.depth))
    | .forRange _ _ e s => 1 + max e.depth s.depth
    | .return_ none     => 1
    | .return_ (some e) => 1 + e.depth
    | .break_           => 1
    | .continue_        => 1
    | .switch_ e cases  => 1 + max e.depth (switchCaseListDepth cases)
    | .doWhile s e      => 1 + max s.depth e.depth

end

-- 基本的な単調性補題

theorem forInit_depth_nonneg (fi : ForInit) : 0 ≤ fi.depth := by
  cases fi <;> simp [ForInit.depth]

theorem expr_depth_pos (e : CppExpr) : 0 < e.depth := by
  cases e with
  | lit l =>
      simp [CppExpr.depth]
  | var x =>
      simp [CppExpr.depth]
  | binop op e1 e2 =>
      have h : 0 < max e1.depth e2.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | unop op e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | assign op e1 e2 =>
      have h : 0 < max e1.depth e2.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | call f args =>
      have h : 0 < max f.depth (exprListDepth args) + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | member e name =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | arrow e name =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | index e1 e2 =>
      have h : 0 < max e1.depth e2.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | addrOf e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | deref e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | ternary c e1 e2 =>
      have h : 0 < max c.depth (max e1.depth e2.depth) + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | cast ty e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | sizeofExpr e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | sizeofType ty =>
      simp [CppExpr.depth]
  | new_ ty initOpt =>
      cases initOpt with
      | none =>
          simp [CppExpr.depth]
      | some val =>
          have h : 0 < val.depth + 1 := Nat.succ_pos _
          simpa [CppExpr.depth, Nat.add_comm] using h
  | delete_ e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h
  | comma e1 e2 =>
      have h : 0 < max e1.depth e2.depth + 1 := Nat.succ_pos _
      simpa [CppExpr.depth, Nat.add_comm] using h

theorem stmt_depth_pos (s : CppStmt) : 0 < s.depth := by
  cases s with
  | skip =>
      simp [CppStmt.depth]
  | expr e =>
      have h : 0 < e.depth + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | block ss =>
      have h : 0 < stmtListDepth ss + 1 := Nat.succ_pos _
      simp [CppStmt.depth, Nat.add_comm,h]
  | decl d =>
      have h : 0 < d.depth + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | ite c t e =>
      have h : 0 < max c.depth (max t.depth e.depth) + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | while_ c body =>
      have h : 0 < max c.depth body.depth + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | for_ init cond step body =>
      have h :
          0 <
            max
              (match init with
               | ForInit.decl d => d.depth
               | ForInit.expr e => e.depth
               | ForInit.none => 0)
              (max
                (match cond with
                 | none => 0
                 | some e => e.depth)
                (max
                  (match step with
                   | none => 0
                   | some e => e.depth)
                  body.depth)) + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, ForInit.depth, Nat.add_comm] using h
  | forRange ty name range body =>
      have h : 0 < max range.depth body.depth + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | return_ ret =>
      cases ret with
      | none =>
          simp [CppStmt.depth]
      | some e =>
          have h : 0 < e.depth + 1 := Nat.succ_pos _
          simpa [CppStmt.depth, Nat.add_comm] using h
  | break_ =>
      simp [CppStmt.depth]
  | continue_ =>
      simp [CppStmt.depth]
  | switch_ e cases =>
      have h : 0 < max e.depth (switchCaseListDepth cases) + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h
  | doWhile body cond =>
      have h : 0 < max body.depth cond.depth + 1 := Nat.succ_pos _
      simpa [CppStmt.depth, Nat.add_comm] using h



-- ============================================================
-- §10. 深さ測度の基本補題（Phase 2 以降のための橋）
-- ============================================================

theorem expr_depth_le_exprListDepth_of_mem
    {e : CppExpr} {es : List CppExpr} :
    e ∈ es → e.depth ≤ exprListDepth es := by
  intro h
  induction es with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp only [List.mem_cons] at h
      simp [exprListDepth]
      rcases h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem stmt_depth_le_stmtListDepth_of_mem
    {s : CppStmt} {ss : List CppStmt} :
    s ∈ ss → s.depth ≤ stmtListDepth ss := by
  intro h
  induction ss with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp only [List.mem_cons] at h
      simp [stmtListDepth]
      rcases h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem switchCase_depth_le_switchCaseListDepth_of_mem
    {c : SwitchCase} {cs : List SwitchCase} :
    c ∈ cs → c.depth ≤ switchCaseListDepth cs := by
  intro h
  induction cs with
  | nil =>
      cases h
  | cons hd tl ih =>
      simp only [List.mem_cons] at h
      simp [switchCaseListDepth]
      rcases h with rfl | htl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem exprListDepth_append (xs ys : List CppExpr) :
    exprListDepth (xs ++ ys) = max (exprListDepth xs) (exprListDepth ys) := by
  induction xs with
  | nil =>
      simp [exprListDepth]
  | cons x xs ih =>
      simp [exprListDepth, ih, Nat.max_assoc, Nat.max_comm]

theorem stmtListDepth_append (xs ys : List CppStmt) :
    stmtListDepth (xs ++ ys) = max (stmtListDepth xs) (stmtListDepth ys) := by
  induction xs with
  | nil =>
      simp [stmtListDepth]
  | cons x xs ih =>
      simp [stmtListDepth, ih, Nat.max_assoc, Nat.max_comm]

theorem switchCaseListDepth_append (xs ys : List SwitchCase) :
    switchCaseListDepth (xs ++ ys) = max (switchCaseListDepth xs) (switchCaseListDepth ys) := by
  induction xs with
  | nil =>
      simp [switchCaseListDepth]
  | cons x xs ih =>
      simp [switchCaseListDepth, ih, Nat.max_assoc, Nat.max_comm]

theorem depth_lt_binop_left (op : BinOp) (e1 e2 : CppExpr) :
    e1.depth < (CppExpr.binop op e1 e2).depth := by
  have h : e1.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_binop_right (op : BinOp) (e1 e2 : CppExpr) :
    e2.depth < (CppExpr.binop op e1 e2).depth := by
  have h : e2.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_unop_arg (op : UnOp) (e : CppExpr) :
    e.depth < (CppExpr.unop op e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_assign_left (op : AssignOp) (e1 e2 : CppExpr) :
    e1.depth < (CppExpr.assign op e1 e2).depth := by
  have h : e1.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_assign_right (op : AssignOp) (e1 e2 : CppExpr) :
    e2.depth < (CppExpr.assign op e1 e2).depth := by
  have h : e2.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_call_fn (f : CppExpr) (args : List CppExpr) :
    f.depth < (CppExpr.call f args).depth := by
  have h : f.depth < max f.depth (exprListDepth args) + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_call_arg_of_mem
    {arg : CppExpr} {f : CppExpr} {args : List CppExpr} :
    arg ∈ args → arg.depth < (CppExpr.call f args).depth := by
  intro hmem
  have h₁ : arg.depth ≤ exprListDepth args :=
    expr_depth_le_exprListDepth_of_mem hmem
  have h₂ : exprListDepth args ≤ max f.depth (exprListDepth args) :=
    Nat.le_max_right _ _
  have h₃ : arg.depth ≤ max f.depth (exprListDepth args) :=
    Nat.le_trans h₁ h₂
  have h₄ : arg.depth < max f.depth (exprListDepth args) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppExpr.depth, Nat.add_comm] using h₄

theorem depth_lt_member_obj (e : CppExpr) (name : Ident) :
    e.depth < (CppExpr.member e name).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_arrow_obj (e : CppExpr) (name : Ident) :
    e.depth < (CppExpr.arrow e name).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_index_left (e1 e2 : CppExpr) :
    e1.depth < (CppExpr.index e1 e2).depth := by
  have h : e1.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_index_right (e1 e2 : CppExpr) :
    e2.depth < (CppExpr.index e1 e2).depth := by
  have h : e2.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_addrOf_arg (e : CppExpr) :
    e.depth < (CppExpr.addrOf e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_deref_arg (e : CppExpr) :
    e.depth < (CppExpr.deref e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_ternary_cond (c e1 e2 : CppExpr) :
    c.depth < (CppExpr.ternary c e1 e2).depth := by
  have h : c.depth < max c.depth (max e1.depth e2.depth) + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_ternary_then (c e1 e2 : CppExpr) :
    e1.depth < (CppExpr.ternary c e1 e2).depth := by
  have h₁ : e1.depth ≤ max e1.depth e2.depth := Nat.le_max_left _ _
  have h₂ : max e1.depth e2.depth ≤ max c.depth (max e1.depth e2.depth) :=
    Nat.le_max_right _ _
  have h₃ : e1.depth ≤ max c.depth (max e1.depth e2.depth) :=
    Nat.le_trans h₁ h₂
  have h₄ : e1.depth < max c.depth (max e1.depth e2.depth) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppExpr.depth, Nat.add_comm] using h₄

theorem depth_lt_ternary_else (c e1 e2 : CppExpr) :
    e2.depth < (CppExpr.ternary c e1 e2).depth := by
  have h₁ : e2.depth ≤ max e1.depth e2.depth := Nat.le_max_right _ _
  have h₂ : max e1.depth e2.depth ≤ max c.depth (max e1.depth e2.depth) :=
    Nat.le_max_right _ _
  have h₃ : e2.depth ≤ max c.depth (max e1.depth e2.depth) :=
    Nat.le_trans h₁ h₂
  have h₄ : e2.depth < max c.depth (max e1.depth e2.depth) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppExpr.depth, Nat.add_comm] using h₄

theorem depth_lt_cast_arg (ty : CppType) (e : CppExpr) :
    e.depth < (CppExpr.cast ty e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_sizeofExpr_arg (e : CppExpr) :
    e.depth < (CppExpr.sizeofExpr e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_new_init (ty : CppType) (e : CppExpr) :
    e.depth < (CppExpr.new_ ty (some e)).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_delete_arg (e : CppExpr) :
    e.depth < (CppExpr.delete_ e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppExpr.depth]

theorem depth_lt_comma_left (e1 e2 : CppExpr) :
    e1.depth < (CppExpr.comma e1 e2).depth := by
  have h : e1.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem depth_lt_comma_right (e1 e2 : CppExpr) :
    e2.depth < (CppExpr.comma e1 e2).depth := by
  have h : e2.depth < max e1.depth e2.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppExpr.depth, Nat.add_comm] using h

theorem init_depth_lt_vardecl_depth (d : VarDecl) :
    d.init.depth < d.depth := by
  cases d with
  | mk ty name init =>
      have h : init.depth < init.depth + 1 := Nat.lt_succ_self _
      simp [VarDecl.depth]

theorem expr_depth_le_initializer_direct (e : CppExpr) :
    e.depth ≤ (Initializer.direct e).depth := by
  simp [Initializer.depth]

theorem expr_depth_le_initializer_list_of_mem
    {e : CppExpr} {es : List CppExpr} :
    e ∈ es → e.depth ≤ (Initializer.list es).depth := by
  intro hmem
  simpa [Initializer.depth] using expr_depth_le_exprListDepth_of_mem hmem

theorem depth_lt_expr_stmt (e : CppExpr) :
    e.depth < (CppStmt.expr e).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppStmt.depth]

theorem depth_lt_block_member
    {s : CppStmt} {ss : List CppStmt} :
    s ∈ ss → s.depth < (CppStmt.block ss).depth := by
  intro hmem
  have h₁ : s.depth ≤ stmtListDepth ss :=
    stmt_depth_le_stmtListDepth_of_mem hmem
  have h₂ : s.depth < stmtListDepth ss + 1 :=
    Nat.lt_succ_of_le h₁
  simpa [CppStmt.depth, Nat.add_comm] using h₂

theorem depth_lt_decl_stmt (d : VarDecl) :
    d.depth < (CppStmt.decl d).depth := by
  have h : d.depth < d.depth + 1 := Nat.lt_succ_self _
  simp [CppStmt.depth]

theorem depth_lt_ite_cond (c : CppExpr) (s1 s2 : CppStmt) :
    c.depth < (CppStmt.ite c s1 s2).depth := by
  have h : c.depth < max c.depth (max s1.depth s2.depth) + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_ite_then (c : CppExpr) (s1 s2 : CppStmt) :
    s1.depth < (CppStmt.ite c s1 s2).depth := by
  have h₁ : s1.depth ≤ max s1.depth s2.depth := Nat.le_max_left _ _
  have h₂ : max s1.depth s2.depth ≤ max c.depth (max s1.depth s2.depth) :=
    Nat.le_max_right _ _
  have h₃ : s1.depth ≤ max c.depth (max s1.depth s2.depth) :=
    Nat.le_trans h₁ h₂
  have h₄ : s1.depth < max c.depth (max s1.depth s2.depth) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppStmt.depth, Nat.add_comm] using h₄

theorem depth_lt_ite_else (c : CppExpr) (s1 s2 : CppStmt) :
    s2.depth < (CppStmt.ite c s1 s2).depth := by
  have h₁ : s2.depth ≤ max s1.depth s2.depth := Nat.le_max_right _ _
  have h₂ : max s1.depth s2.depth ≤ max c.depth (max s1.depth s2.depth) :=
    Nat.le_max_right _ _
  have h₃ : s2.depth ≤ max c.depth (max s1.depth s2.depth) :=
    Nat.le_trans h₁ h₂
  have h₄ : s2.depth < max c.depth (max s1.depth s2.depth) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppStmt.depth, Nat.add_comm] using h₄

theorem depth_lt_while_cond (c : CppExpr) (body : CppStmt) :
    c.depth < (CppStmt.while_ c body).depth := by
  have h : c.depth < max c.depth body.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_while_body (c : CppExpr) (body : CppStmt) :
    body.depth < (CppStmt.while_ c body).depth := by
  have h : body.depth < max c.depth body.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_forRange_range (ty : CppType) (name : Ident) (e : CppExpr) (body : CppStmt) :
    e.depth < (CppStmt.forRange ty name e body).depth := by
  have h : e.depth < max e.depth body.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_forRange_body (ty : CppType) (name : Ident) (e : CppExpr) (body : CppStmt) :
    body.depth < (CppStmt.forRange ty name e body).depth := by
  have h : body.depth < max e.depth body.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_return_expr (e : CppExpr) :
    e.depth < (CppStmt.return_ (some e)).depth := by
  have h : e.depth < e.depth + 1 := Nat.lt_succ_self _
  simp [CppStmt.depth]

theorem depth_lt_switch_expr (e : CppExpr) (cases : List SwitchCase) :
    e.depth < (CppStmt.switch_ e cases).depth := by
  have h : e.depth < max e.depth (switchCaseListDepth cases) + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_switch_case_member
    {c : SwitchCase} {e : CppExpr} {cases : List SwitchCase} :
    c ∈ cases → c.depth < (CppStmt.switch_ e cases).depth := by
  intro hmem
  have h₁ : c.depth ≤ switchCaseListDepth cases :=
    switchCase_depth_le_switchCaseListDepth_of_mem hmem
  have h₂ : switchCaseListDepth cases ≤ max e.depth (switchCaseListDepth cases) :=
    Nat.le_max_right _ _
  have h₃ : c.depth ≤ max e.depth (switchCaseListDepth cases) :=
    Nat.le_trans h₁ h₂
  have h₄ : c.depth < max e.depth (switchCaseListDepth cases) + 1 :=
    Nat.lt_succ_of_le h₃
  simpa [CppStmt.depth, Nat.add_comm] using h₄

theorem depth_lt_doWhile_body (body : CppStmt) (cond : CppExpr) :
    body.depth < (CppStmt.doWhile body cond).depth := by
  have h : body.depth < max body.depth cond.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_left _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

theorem depth_lt_doWhile_cond (body : CppStmt) (cond : CppExpr) :
    cond.depth < (CppStmt.doWhile body cond).depth := by
  have h : cond.depth < max body.depth cond.depth + 1 :=
    Nat.lt_succ_of_le (Nat.le_max_right _ _)
  simpa [CppStmt.depth, Nat.add_comm] using h

-- ============================================================
-- §10. 使用例（サニティチェック）
-- ============================================================

section Examples

  -- int add(int x, int y) { return x + y; }
  def exampleAdd : FuncDef := {
    returnType := CInt,
    name       := "add",
    params     := [
      { type := CInt, name := "x", default := none },
      { type := CInt, name := "y", default := none }
    ],
    body := .block [
      .return_ (some (.binop .add (.var "x") (.var "y")))
    ]
  }

  -- int factorial(int n) {
  --   if (n <= 1) return 1;
  --   return n * factorial(n - 1);
  -- }
  def exampleFactorial : FuncDef := {
    returnType := CInt,
    name       := "factorial",
    params     := [{ type := CInt, name := "n", default := none }],
    body := .block [
      .ite (.binop .le (.var "n") (.lit (.int 1)))
           (.return_ (some (.lit (.int 1))))
           .skip,
      .return_ (some
        (.binop .mul
          (.var "n")
          (.call (.var "factorial")
                 [.binop .sub (.var "n") (.lit (.int 1))])))
    ]
  }

  -- int arr[5];
  -- arr[2] = 42;  (NoUB仮定: 2 < 5 は保証される)
  def exampleArray : CppStmt :=
    .block [
      .decl { type := .array CInt 5, name := "arr", init := .none },
      .expr (.assign .assign
               (.index (.var "arr") (.lit (.int 2)))
               (.lit (.int 42)))
    ]
/- -/
  -- 深さのサニティチェック
 -- #eval exampleAdd.body.depth          -- 期待値: 4
 -- #eval exampleFactorial.body.depth    -- 期待値: 6
  --#eval exampleArray.depth             -- 期待値: 5

end Examples

end Cpp
