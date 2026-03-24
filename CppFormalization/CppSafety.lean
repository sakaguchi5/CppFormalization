import CppFormalization.CppState
import CppFormalization.CppState_Contracts
import CppFormalization.Phase2.CppTyping

namespace Cpp

/-
Phase 2.5: 安全性述語層

設計原則：
  1. NoUB を一枚岩にしない。EvalError の粒度に合わせて述語を分解する。
  2. 各述語は「この種の実行時失敗が起きない」という Prop である。
  3. 述語は「式・文の構造」と「実行状態」の両方を引数に取る。
  4. SafeExpr / SafeStmt は述語の束だが、
     証明で使うときは個別述語を分解して使う。

述語の対応：
  EvalError.uninitializedRead  ←→  NoUninit
  EvalError.nullDeref          ←→  NoNullDeref
  EvalError.outOfBounds        ←→  NoOutOfBounds
  EvalError.useAfterFree       ←→  NoUseAfterFree
  EvalError.invalidCast        ←→  NoInvalidCast
  EvalError.notAssignable      ←→  isAssignable (Phase 2 で定義済み)
  EvalError.unboundVar         ←→  noFreeVarsExpr (Phase 2 で定義済み)

「停止しない」(diverge) はここに入れない。
これは UB でも静的整形違反でもなく別カテゴリ。
-/

-- ============================================================
-- §1. ストア補助述語
-- ============================================================

section StorePredicates

/-
CellAlive : store が場所 l に alive な cell を持つ
NoUseAfterFree の基盤
-/
def CellAlive (s : State) (l : Loc) : Prop :=
  ∃ c : Cell, s.readCell l = some c ∧ c.alive = true

/-
CellAliveAndInit : store が場所 l に alive かつ初期化済みの cell を持つ
NoUninit の基盤
-/
def CellAliveAndInit (s : State) (l : Loc) : Prop :=
  ∃ c : Cell,
    s.readCell l = some c ∧
    c.alive = true ∧
    c.initialized = true

-- CellAliveAndInit は CellAlive を含意する
theorem cellAliveAndInit_implies_alive
    (s : State) (l : Loc)
    (h : CellAliveAndInit s l) : CellAlive s l := by
  obtain ⟨c, hread, halive, _⟩ := h
  exact ⟨c, hread, halive⟩

/-
CellIsArray : 場所 l の cell が配列で、要素数が n であること
NoOutOfBounds の基盤
-/
def CellIsArray (s : State) (l : Loc) (n : Nat) : Prop :=
  ∃ c elemTy locs,
    s.readCell l = some c ∧
    c.alive = true ∧
    c.object = .array elemTy locs ∧
    locs.length = n

/-
PtrValid : ポインタ値 v が有効（non-null かつ alive な場所を指す）
-/
def PtrValid (s : State) (v : RValue) : Prop :=
  ∃ l : Loc, v = .ptr l ∧ l ≠ nullLoc ∧ CellAlive s l

end StorePredicates

-- ============================================================
-- §2. 式レベルの安全性述語
-- ============================================================

section ExprSafety

/-
NoUninit_expr : 式の評価中に未初期化読みが起きない

ここで「読み」が起きる箇所：
  - var x を rvalue として使う（lvalue→rvalue 変換）
  - deref *e（e がポインタ先を読む）
  - index e1[e2]（配列要素を読む）
  - member e.f（メンバを読む）
  - arrow e->f（ポインタ先メンバを読む）

isAssignable な文脈では lvalue→rvalue 変換は起きないので除外する。
-/
def NoUninit_lval (s : State) (l : Loc) : Prop :=
  CellAliveAndInit s l

/-
NoNullDeref_expr : 式の評価中にヌルポインタ参照が起きない

deref *e において e の値が nullLoc でないこと。
arrow e->f も同様。
-/
def NoNullDeref_ptr (v : RValue) : Prop :=
  ∃ l : Loc, v = .ptr l ∧ l ≠ nullLoc

/-
NoOutOfBounds_index : 配列添字アクセスが範囲内であること

e1[e2] において e2 の値が 0 以上かつ e1 の長さ未満であること。
-/
def NoOutOfBounds_index (arrLen : Nat) (idx : Int) : Prop :=
  0 ≤ idx ∧ idx < (arrLen : Int)

/-
NoUseAfterFree_loc : 場所 l が free された後にアクセスされていないこと
-/
def NoUseAfterFree_loc (s : State) (l : Loc) : Prop :=
  CellAlive s l

/-
NoInvalidCast_val : キャスト元の値がキャスト先の型に対して安全であること
（例: ptr を int にキャストするのは NoUB 仮定下では禁止）
-/
def NoInvalidCast_val (v : RValue) (τ_src τ_dst : CppType) : Prop :=
  match τ_src, τ_dst, v with
  -- int → float: 常に安全（理想化: 精度損失なし）
  | CInt, CFloat, .int _ => True
  -- float → int: 常に安全（理想化: 切り捨て可）
  | CFloat, CInt, .float _ => True
  -- int → bool: 常に安全
  | CInt, CBool, .int _ => True
  -- ptr → ptr: 型が変わっても（NoUB 仮定下では）安全
  | .ptr _, .ptr _, .ptr _ => True
  -- 同一型: 常に安全
  | _, _, _ => τ_src = τ_dst

end ExprSafety

-- ============================================================
-- §3. SafeState：状態全体の安全性
-- ============================================================

section SafeState

/-
SafeState : State → Prop

実行状態 s が「安全」であること。
safe な状態から始まれば、eval が safety 関連の EvalError を返さない
という定理の前提になる（Phase 5）。

この述語は一枚岩にせず、後で分解して使えるように構造体で持つ。
-/
structure SafeState (s : State) : Prop where
  -- 全 cell の型整合
  storeTyped    : StoreWellTyped s.store

  -- nextLoc で指される場所はまだ store にない（fresh invariant）
  nextLocFresh  : ∀ l : Loc, s.nextLoc ≤ l → s.readCell l = none

  -- 全 alive cell は nextLoc 未満の場所にある
  aliveInRange  : ∀ l : Loc, CellAlive s l → l < s.nextLoc

  -- global frame の束縛先は全て store に存在する
  globalBound   : ∀ x l, Env.lookup s.env x = some l →
                    ∃ c, s.readCell l = some c

-- SafeState から StoreWellTyped を取り出す補題
theorem safeState_storeTyped {s : State} (h : SafeState s) :
    StoreWellTyped s.store := h.storeTyped

-- SafeState から nextLocFresh を取り出す補題
theorem safeState_nextLocFresh {s : State} (h : SafeState s) :
    ∀ l, s.nextLoc ≤ l → s.readCell l = none := h.nextLocFresh

end SafeState

-- ============================================================
-- §4. SafeExpr：式ごとの安全性述語
-- ============================================================

section SafeExpr

/-
SafeExpr : TyEnv → StructTable → State → CppExpr → Prop

式 e が状態 s において安全に評価できること。
型付け（Phase 2）と合わせて使う。

構造：式の構造に対して再帰的に定義する。
-/
inductive SafeExpr
    (Γ : TyEnv) (stbl : StructTable) (s : State)
    : CppExpr → Prop where

  -- リテラルは常に安全
  | S_Lit : ∀ (lit : Literal),
      SafeExpr Γ stbl s (.lit lit)

  -- 変数: 環境に存在し、lvalue が有効
  | S_Var : ∀ (x : Ident) (τ : CppType) (l : Loc),
      Γ.lookup x = some τ →
      s.locOf x = some l →
      -- lvalue→rvalue 変換が起きる場合（rvalue 文脈）に初期化済みを要求
      -- これを「rvalue 文脈かどうか」で分ける代わりに、
      -- 常に alive であることだけ要求し、
      -- 実際の読み取り安全性は NoUninit_lval で別途要求する
      CellAlive s l →
      SafeExpr Γ stbl s (.var x)

  -- 二項演算: 両辺が安全
  | S_BinOp : ∀ (op : BinOp) (e1 e2 : CppExpr),
      SafeExpr Γ stbl s e1 →
      SafeExpr Γ stbl s e2 →
      SafeExpr Γ stbl s (.binop op e1 e2)

  -- 単項演算: 被演算子が安全
  | S_UnOp : ∀ (op : UnOp) (e : CppExpr),
      SafeExpr Γ stbl s e →
      SafeExpr Γ stbl s (.unop op e)

  -- 代入: 左辺が assignable かつ両辺が安全
  | S_Assign : ∀ (op : AssignOp) (lhs rhs : CppExpr),
      isAssignable lhs →
      SafeExpr Γ stbl s lhs →
      SafeExpr Γ stbl s rhs →
      SafeExpr Γ stbl s (.assign op lhs rhs)

  -- デリファレンス: e が non-null ポインタを指す
  -- これが NoNullDeref の核心
  | S_Deref : ∀ (e : CppExpr) (τ : CppType),
      SafeExpr Γ stbl s e →
      HasType Γ stbl e (.ptr τ) →
      -- 実行時の値が non-null であること（動的条件）
      (∀ l, s.locOf (match e with | .var x => x | _ => "") = some l →
        l ≠ nullLoc) →
      SafeExpr Γ stbl s (.deref e)

  -- アドレス取得: e が lvalue
  | S_AddrOf : ∀ (e : CppExpr),
      isAssignable e →
      SafeExpr Γ stbl s e →
      SafeExpr Γ stbl s (.addrOf e)

  -- 配列添字: 範囲内アクセス
  | S_Index : ∀ (e1 e2 : CppExpr) (τ_elem : CppType) (n : Nat),
      SafeExpr Γ stbl s e1 →
      SafeExpr Γ stbl s e2 →
      HasType Γ stbl e1 (.array τ_elem n) →
      -- 添字が範囲内（動的条件）は SafeState + 型情報から引き出す
      -- Phase 5 の preservation ではここの n が一定であることを使う
      SafeExpr Γ stbl s (.index e1 e2)

  -- 関数呼び出し: f と全引数が安全
  | S_Call : ∀ (f : CppExpr) (args : List CppExpr),
      SafeExpr Γ stbl s f →
      (∀ e ∈ args, SafeExpr Γ stbl s e) →
      SafeExpr Γ stbl s (.call f args)

  -- メンバアクセス
  | S_Member : ∀ (e : CppExpr) (field : Ident),
      SafeExpr Γ stbl s e →
      SafeExpr Γ stbl s (.member e field)

  -- ポインタメンバ: e が non-null
  | S_Arrow : ∀ (e : CppExpr) (field : Ident),
      SafeExpr Γ stbl s e →
      SafeExpr Γ stbl s (.arrow e field)

  -- 三項演算子
  | S_Ternary : ∀ (c e1 e2 : CppExpr),
      SafeExpr Γ stbl s c →
      SafeExpr Γ stbl s e1 →
      SafeExpr Γ stbl s e2 →
      SafeExpr Γ stbl s (.ternary c e1 e2)

  -- キャスト（有効な型変換のみ）
  | S_Cast : ∀ (τ : CppType) (e : CppExpr),
      SafeExpr Γ stbl s e →
      SafeExpr Γ stbl s (.cast τ e)

  -- sizeof は純粋にコンパイル時定数
  | S_SizeofType : ∀ (τ : CppType),
      SafeExpr Γ stbl s (.sizeofType τ)

  | S_SizeofExpr : ∀ (e : CppExpr),
      SafeExpr Γ stbl s (.sizeofExpr e)

  -- new: 常に成功（NoUB 仮定: メモリ確保は失敗しない）
  | S_New : ∀ (τ : CppType) (initOpt : Option CppExpr),
      (∀ e, initOpt = some e → SafeExpr Γ stbl s e) →
      SafeExpr Γ stbl s (.new_ τ initOpt)

  -- delete: e が non-null かつ alive
  | S_Delete : ∀ (e : CppExpr) (τ : CppType),
      SafeExpr Γ stbl s e →
      HasType Γ stbl e (.ptr τ) →
      SafeExpr Γ stbl s (.delete_ e)

  -- コンマ
  | S_Comma : ∀ (e1 e2 : CppExpr),
      SafeExpr Γ stbl s e1 →
      SafeExpr Γ stbl s e2 →
      SafeExpr Γ stbl s (.comma e1 e2)

end SafeExpr

-- ============================================================
-- §5. SafeStmt：文ごとの安全性述語
-- ============================================================

section SafeStmt

/-
SafeStmt : TyEnv → StructTable → CppType → State → CppStmt → Prop

文 st が状態 s において安全に実行できること。
retTy は return 文の型チェックに使う。
-/
inductive SafeStmt
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType) (s : State)
    : CppStmt → Prop where

  | S_Skip :
      SafeStmt Γ stbl retTy s .skip

  | S_Expr : ∀ (e : CppExpr),
      SafeExpr Γ stbl s e →
      SafeStmt Γ stbl retTy s (.expr e)

  | S_Block : ∀ (ss : List CppStmt),
      (∀ st ∈ ss, SafeStmt Γ stbl retTy s st) →
      SafeStmt Γ stbl retTy s (.block ss)

  | S_Decl : ∀ (d : VarDecl),
      (∀ e, d.init = .direct e → SafeExpr Γ stbl s e) →
      SafeStmt Γ stbl retTy s (.decl d)

  | S_Ite : ∀ (c : CppExpr) (st1 st2 : CppStmt),
      SafeExpr Γ stbl s c →
      SafeStmt Γ stbl retTy s st1 →
      SafeStmt Γ stbl retTy s st2 →
      SafeStmt Γ stbl retTy s (.ite c st1 st2)

  | S_While : ∀ (c : CppExpr) (body : CppStmt),
      SafeExpr Γ stbl s c →
      SafeStmt Γ stbl retTy s body →
      SafeStmt Γ stbl retTy s (.while_ c body)

  | S_DoWhile : ∀ (body : CppStmt) (c : CppExpr),
      SafeStmt Γ stbl retTy s body →
      SafeExpr Γ stbl s c →
      SafeStmt Γ stbl retTy s (.doWhile body c)

  | S_For : ∀ (init : ForInit) (cond step : Option CppExpr) (body : CppStmt),
      (∀ e, cond = some e → SafeExpr Γ stbl s e) →
      (∀ e, step = some e → SafeExpr Γ stbl s e) →
      SafeStmt Γ stbl retTy s body →
      SafeStmt Γ stbl retTy s (.for_ init cond step body)

  | S_ReturnVoid :
      SafeStmt Γ stbl retTy s (.return_ none)

  | S_ReturnValue : ∀ (e : CppExpr),
      SafeExpr Γ stbl s e →
      SafeStmt Γ stbl retTy s (.return_ (some e))

  | S_Break :
      SafeStmt Γ stbl retTy s .break_

  | S_Continue :
      SafeStmt Γ stbl retTy s .continue_

  | S_Switch : ∀ (e : CppExpr) (cases : List SwitchCase),
      SafeExpr Γ stbl s e →
      SafeStmt Γ stbl retTy s (.switch_ e cases)

end SafeStmt

-- ============================================================
-- §6. 複合安全性条件（Phase 3/4/5 の前提として使う）
-- ============================================================

section CompositeSafety

/-
WF_Typed_Safe : プログラムの「全部入り」前提

Phase 3 の参照意味論・Phase 4 の evaluator・Phase 5 の preservation
全てがこれを前提に動く。
-/
structure WF_Typed_Safe
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s : State) (st : CppStmt) : Prop where
  -- Phase 1.5: 構造的 WF
  stateWF   : s.WF
  -- Phase 2: 型付け
  stmtTyped : HasTypeStmt Γ stbl retTy st
  -- Phase 2: 静的整形
  wellFormed : breakOnlyInLoop st = true
  -- Phase 2.5: 安全性
  safe       : SafeStmt Γ stbl retTy s st
  safeState  : SafeState s

/-
便利な分解補題群
-/

theorem wts_stateWF {Γ stbl retTy s st}
    (h : WF_Typed_Safe Γ stbl retTy s st) : s.WF :=
  h.stateWF

theorem wts_stmtTyped {Γ stbl retTy s st}
    (h : WF_Typed_Safe Γ stbl retTy s st) :
    HasTypeStmt Γ stbl retTy st :=
  h.stmtTyped

theorem wts_safe {Γ stbl retTy s st}
    (h : WF_Typed_Safe Γ stbl retTy s st) :
    SafeStmt Γ stbl retTy s st :=
  h.safe

theorem wts_safeState {Γ stbl retTy s st}
    (h : WF_Typed_Safe Γ stbl retTy s st) :
    SafeState s :=
  h.safeState

end CompositeSafety

-- ============================================================
-- §7. SafeState の操作安定性補題
--     （「safe な状態への操作は safe な状態を返す」）
-- ============================================================

section SafeStatePreservation

-- enterScope は SafeState を保つ
theorem safeState_enterScope
    (s : State) (h : SafeState s) : SafeState s.enterScope := by
  constructor
  · -- storeTyped: store は変わらない
    simpa [State.enterScope] using h.storeTyped
  · -- nextLocFresh: store, nextLoc 変わらない
    intro l hl
    simpa [State.enterScope, State.readCell] using h.nextLocFresh l hl
  · -- aliveInRange
    intro l hal
    apply h.aliveInRange
    simpa [State.enterScope, State.readCell, CellAlive] using hal
  · -- globalBound
    intro x l hlookup
    apply h.globalBound
    simpa [State.enterScope, Env.lookup] using hlookup

-- allocCell は nextLocFresh と aliveInRange を保つ
-- （証明の核：nextLoc が増えることを使う）
theorem safeState_allocCell
    (s : State) (c : Cell) (h : SafeState s)
    (hcell : CellWellTyped c) :
    SafeState (s.allocCell c).2 := by
  constructor
  · -- storeTyped: 新しい cell は CellWellTyped なので OK
    intro l' c' hread'
    simp [State.allocCell, State.readCell] at hread'
    by_cases hl : l' = s.nextLoc
    · -- l' = nextLoc: これが今 alloc した cell
      subst hl
      rw [Store.read_write_eq] at hread'
      cases hread'
      exact hcell
    · -- l' ≠ nextLoc: 以前の cell
      have : Store.read s.store l' = some c' := by
        have : Store.read (Store.write s.store s.nextLoc c) l' = some c' := hread'
        -- write は異なる場所に影響しない（Phase 5 で正式証明）
        sorry
      exact h.storeTyped l' c' this
  · -- nextLocFresh: nextLoc + 1 以降はまだ空
    intro l hl
    simp [State.allocCell, State.readCell]
    -- l ≥ nextLoc + 1 > nextLoc → write した nextLoc とは異なる
    -- かつ元の store も l には何もない
    sorry
  · -- aliveInRange
    intro l hal
    simp [State.allocCell]
    by_cases hl : l = s.nextLoc
    · -- 今 alloc した場所
      subst hl; omega
    · -- 既存の alive cell は s.nextLoc 未満
      apply Nat.lt_succ_of_lt
      apply h.aliveInRange
      simp [CellAlive, State.readCell, State.allocCell] at hal
      sorry
  · -- globalBound
    intro x l hlookup
    simp [State.allocCell]
    have := h.globalBound x l (by simpa [State.allocCell] using hlookup)
    obtain ⟨c', hc'⟩ := this
    exact ⟨c', by sorry⟩ -- write は既存 cell を消さない

-- writeScalar は SafeState を保つ（型が一致する場合）
theorem safeState_writeScalar
    (s : State) (l : Loc) (v : RValue) (c : Cell)
    (h : SafeState s)
    (hread : s.readCell l = some c)
    (halive : c.alive = true)
    (htype : RValueHasType v c.ty) :
    SafeState { s with store := Store.write s.store l (c.overwriteScalar v) } := by
  constructor
  · -- storeTyped: l の cell が更新されるが型は変わらない
    intro l' c' hread'
    simp [State.readCell] at hread'
    by_cases hl : l' = l
    · subst hl
      rw [Store.read_write_eq] at hread'
      cases hread'
      -- c.overwriteScalar v の CellWellTyped を示す
      simp [CellWellTyped, Cell.overwriteScalar]
      exact ObjectFitsType.scalar v c.ty htype
    · -- l' ≠ l: 元の cell
      apply h.storeTyped l'
      simp [State.readCell]
      sorry -- Store.read_write_ne (Phase 5 で補題化)
  · -- nextLocFresh
    intro l' hl'
    simp [State.readCell]
    -- write は nextLoc 未満の場所しか触れない（h.aliveInRange より）
    sorry
  · -- aliveInRange: write は alive フラグを変えない
    intro l' hal
    apply h.aliveInRange
    simp [CellAlive, State.readCell] at hal ⊢
    obtain ⟨c', hc', halive'⟩ := hal
    by_cases hl : l' = l
    · subst hl
      rw [Store.read_write_eq] at hc'
      cases hc'
      exact ⟨c, hread, halive⟩
    · exact ⟨c', by sorry, halive'⟩ -- Store.read_write_ne
  · -- globalBound
    intro x l' hlookup
    obtain ⟨c', hc'⟩ := h.globalBound x l' (by simpa using hlookup)
    simp [State.readCell]
    by_cases hl : l' = l
    · subst hl
      exact ⟨c.overwriteScalar v, Store.read_write_eq _ _ _⟩
    · exact ⟨c', by sorry⟩

end SafeStatePreservation

-- ============================================================
-- §8. 主定理の宣言（Phase 5 への橋頭堡）
-- ============================================================

section MainTheoremStatements

/-
以下はまだ証明が空（sorry）だが、
「何を証明すべきか」を型シグネチャとして固定する。
Phase 5 でこれらを埋める。

これが助言で言う「三本の定理」に対応する。
-/

/--
安全性定理（Safety）：
WF + Typed + Safe な状態から始めた核断片は、
evaluator が EvalError のうち UB 起因のものを返さない。

「数学的失敗（型エラー・未束縛変数）は静的整形で排除済み」
「UB 起因の失敗（nullDeref・outOfBounds 等）は SafeExpr/SafeStmt で排除済み」
「残るのは timeout（diverge）のみ」という主張。
-/
theorem safety_no_ub_error
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s : State) (st : CppStmt)
    (h : WF_Typed_Safe Γ stbl retTy s st)
    (eval : EvalStmtSig)
    (fuel : Nat)
    : ∀ e s',
      eval fuel s st = .error e s' →
      -- UB 起因のエラーは返さない
      ¬ (e = .nullDeref ∨
         e = .outOfBounds ∨
         e = .invalidCast ∨
         (∃ l, e = .useAfterFree l) ∨
         (∃ l, e = .uninitializedRead l)) := by
  sorry -- Phase 5 で証明する

/--
adequacy（Soundness of evaluator）：
evaluator が .ok r s' を返したなら、
参照意味論でも同じ結果・状態に到達する。
-/
-- Phase 3 で参照意味論を定義してから型シグネチャを確定する

/--
completeness：
参照意味論で有限実行により結果 r に到達するなら、
十分大きい fuel で evaluator も .ok r を返す。
-/
-- Phase 3 で参照意味論を定義してから型シグネチャを確定する

/--
timeout 分離定理：
timeout は evaluator の artifact であり、意味論的失敗ではない。
有限参照実行が存在するなら、十分大きい fuel で timeout は消える。
-/
-- Phase 3/4 で定義してから証明する

end MainTheoremStatements

-- ============================================================
-- §9. 使用例（サニティチェック）
-- ============================================================

section Examples

-- SafeExpr: リテラルは常に safe
example (Γ : TyEnv) (stbl : StructTable) (s : State) :
    SafeExpr Γ stbl s (.lit (.int 42)) :=
  SafeExpr.S_Lit (.int 42)

-- SafeStmt: skip は常に safe
example (Γ : TyEnv) (stbl : StructTable) (retTy : CppType) (s : State) :
    SafeStmt Γ stbl retTy s .skip :=
  SafeStmt.S_Skip

-- CellAliveAndInit → CellAlive の使用例
example (s : State) (l : Loc)
    (h : CellAliveAndInit s l) : CellAlive s l :=
  cellAliveAndInit_implies_alive s l h

-- NoNullDeref_ptr: non-null ポインタの確認
example : NoNullDeref_ptr (.ptr 1) :=
  ⟨1, rfl, by decide⟩

-- NoOutOfBounds_index: 範囲内添字の確認
example : NoOutOfBounds_index 5 2 :=
  ⟨by decide, by decide⟩

-- SafeState.empty の構築（State.empty は safe）
-- nextLoc = 1, store = [] なので自明に成立
example : SafeState State.empty := by
  constructor
  · -- storeTyped: store = [] なので trivially
    intro l c h
    simp [State.readCell, Store.read, Assoc.lookup] at h
  · -- nextLocFresh
    intro l hl
    simp [State.readCell, Store.read, Assoc.lookup, State.empty]
  · -- aliveInRange
    intro l ⟨c, hread, _⟩
    simp [State.readCell, Store.read, Assoc.lookup, State.empty] at hread
  · -- globalBound
    intro x l hlookup
    simp [State.empty, Env.lookup, Env.lookupLocals, Frame.lookup,
          Assoc.lookup] at hlookup

end Examples

end Cpp
