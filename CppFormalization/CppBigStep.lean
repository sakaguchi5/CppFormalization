import CppFormalization.CppState
import CppFormalization.CppState_Contracts
import CppFormalization.Phase2.CppTyping
import CppFormalization.Phase2_5.CppSafety

namespace Cpp

/-
Phase 3: 参照意味論（Reference Semantics）

設計方針：
  - big-step 帰納的関係として定義する（関数ではなく命題）
  - これが evaluator（Phase 4）の「仕様」になる
  - 核断片のみ扱う：
      式: lit / var / addrOf / deref / binop / pureUnop /
          preinc / postinc / predec / postdec / assign /
          ternary / comma / cast(3種)
      文: skip / expr / block / decl / ite / return / break / continue
  - while / for / function call は Phase 4 以降
  - diverge（停止しない）は意図的に規則を持たない
    → 有限実行のみが bigStep 関係を持つ
  - EvalError.divByZero に相当する「0除算」は
    evalBinOp が none を返すことで stuck 扱いとなる
    （NoUB 仮定下: 0除算が起きないことは SafeExpr の義務）

記法：
  s ⊢ e ⇓ᵉ (r, s')    BigStepExpr s e r s'
  s ⊢ e ⇓ᵛ (v, s')    BigStepExprRVal s e v s'
  s ⊢ st ⇓ˢ (ctrl, s') BigStepStmt s st ctrl s'
-/

-- ============================================================
-- §1. 算術意味論（純粋関数）
-- ============================================================

section Arithmetic

/-- リテラルを RValue に変換 -/
def interpretLiteral : Literal → RValue
  | .int n    => .int n
  | .uint n   => .uint n
  | .float f  => .float f
  | .double f => .float f   -- 理想化: float/double を統一
  | .bool b   => .bool b
  | .char c   => .int c.toNat
  | .null     => .ptr nullLoc

/--
二項演算の純粋意味論。
none は「この組み合わせに規則なし」= semantics は stuck。
NoUB 仮定下では div/mod の n2=0 は SafeExpr で排除される。
-/
def evalBinOp (op : BinOp) (v1 v2 : RValue) : Option RValue :=
  match op, v1, v2 with
  -- 整数演算（理想化: ℤ、オーバーフローなし）
  | .add, .int n1, .int n2  => some (.int (n1 + n2))
  | .sub, .int n1, .int n2  => some (.int (n1 - n2))
  | .mul, .int n1, .int n2  => some (.int (n1 * n2))
  | .div, .int n1, .int n2  => if n2 = 0 then none else some (.int (n1 / n2))
  | .mod, .int n1, .int n2  => if n2 = 0 then none else some (.int (n1 % n2))
  -- 浮動小数演算（理想化: ℝ）
  | .add, .float f1, .float f2 => some (.float (f1 + f2))
  | .sub, .float f1, .float f2 => some (.float (f1 - f2))
  | .mul, .float f1, .float f2 => some (.float (f1 * f2))
  | .div, .float f1, .float f2 => some (.float (f1 / f2))
  -- 整数比較
  | .eq, .int n1, .int n2  => some (.bool (n1 == n2))
  | .ne, .int n1, .int n2  => some (.bool (n1 != n2))
  | .lt, .int n1, .int n2  => some (.bool (n1 < n2))
  | .le, .int n1, .int n2  => some (.bool (n1 ≤ n2))
  | .gt, .int n1, .int n2  => some (.bool (n1 > n2))
  | .ge, .int n1, .int n2  => some (.bool (n1 ≥ n2))
  -- bool 等値
  | .eq, .bool b1, .bool b2 => some (.bool (b1 == b2))
  | .ne, .bool b1, .bool b2 => some (.bool (b1 != b2))
  -- 論理演算
  | .and, .bool b1, .bool b2 => some (.bool (b1 && b2))
  | .or,  .bool b1, .bool b2 => some (.bool (b1 || b2))
  -- ポインタ等値
  | .eq, .ptr l1, .ptr l2 => some (.bool (l1 == l2))
  | .ne, .ptr l1, .ptr l2 => some (.bool (l1 != l2))
  | _, _, _                => none

/-- 副作用のない単項演算 -/
def evalPureUnOp (op : UnOp) (v : RValue) : Option RValue :=
  match op, v with
  | .neg,    .int n   => some (.int (-n))
  | .neg,    .float f => some (.float (-f))
  | .not,    .bool b  => some (.bool (!b))
  | .bitNot, .int n   => some (.int (~~~n))
  | _,       _        => none

/--
複合代入演算子の新値計算。
.assign の場合は v1（現在値）を無視して v2 を返す。
-/
def evalAssignOp (op : AssignOp) (v1 v2 : RValue) : Option RValue :=
  match op with
  | .assign     => some v2
  | .addAssign  => evalBinOp .add v1 v2
  | .subAssign  => evalBinOp .sub v1 v2
  | .mulAssign  => evalBinOp .mul v1 v2
  | .divAssign  => evalBinOp .div v1 v2
  | .modAssign  => evalBinOp .mod v1 v2
  | .shlAssign  => evalBinOp .shl v1 v2
  | .shrAssign  => evalBinOp .shr v1 v2
  | .bitAndAssign => evalBinOp .bitAnd v1 v2
  | .bitOrAssign  => evalBinOp .bitOr v1 v2
  | .bitXorAssign => evalBinOp .bitXor v1 v2

end Arithmetic

-- ============================================================
-- §2. lval→rval 変換関係
-- ============================================================

section LValConversion

/-
LValToRVal : State → ExprResult → RValue → Prop

ExprResult（lval か rval）を RValue に変換する。
- rval はそのまま
- lval は store から読む（alive かつ initialized かつ scalar が必要）

状態を変更しない（読み取りは純粋）。
-/
inductive LValToRVal : State → ExprResult → RValue → Prop where

  -- rval はすでに値なのでそのまま
  | ofRVal : ∀ (s : State) (v : RValue),
      LValToRVal s (.rval v) v

  -- lval は store から読む
  -- alive・initialized・scalar の三条件を明示
  | ofLVal : ∀ (s : State) (l : Loc) (c : Cell) (v : RValue),
      s.readCell l = some c →
      c.alive = true →
      c.initialized = true →
      c.object = .scalar v →
      LValToRVal s (.lval l) v

end LValConversion

-- ============================================================
-- §3. 式・文の big-step 関係（相互帰納的定義）
-- ============================================================

/-
式評価と文評価の相互帰納的定義。

依存関係:
  BigStepExpr    ←→  BigStepExprRVal (相互再帰)
  BigStepStmt    ←→  BigStepStmts    (相互再帰)
  BigStepStmt         uses BigStepExprRVal (先に定義済)
-/

-- ──────────────────────────────────────────────
-- 式の big-step 関係
-- ──────────────────────────────────────────────

mutual

  /-
  BigStepExpr s e r s'

  状態 s で式 e を評価すると ExprResult r と新状態 s' が得られる。
  r が lval の場合、それは「書き込み可能な場所」を表す。
  r が rval の場合、それは「計算済みの値」を表す。
  -/
  inductive BigStepExpr : State → CppExpr → ExprResult → State → Prop where

    -- ── リテラル ─────────────────────────────────────
    -- リテラルは常に rval を返す。状態は変化しない。
    | E_Lit : ∀ (s : State) (lit : Literal),
        BigStepExpr s (.lit lit) (.rval (interpretLiteral lit)) s

    -- ── 変数 ──────────────────────────────────────────
    -- 変数は lval（その場所）を返す。状態は変化しない。
    | E_Var : ∀ (s : State) (x : Ident) (l : Loc),
        s.locOf x = some l →
        BigStepExpr s (.var x) (.lval l) s

    -- ── アドレス取得 ──────────────────────────────────
    -- &e : e が lval l に評価されるなら &e は rval (ptr l)。
    | E_AddrOf : ∀ (s s' : State) (e : CppExpr) (l : Loc),
        BigStepExpr s e (.lval l) s' →
        BigStepExpr s (.addrOf e) (.rval (.ptr l)) s'

    -- ── デリファレンス ────────────────────────────────
    -- *e : e が rval (ptr l) に評価され、l ≠ nullLoc なら
    -- *e は lval l（その場所）を返す。
    -- NoNullDeref 条件は SafeExpr から来る。
    | E_Deref : ∀ (s s' : State) (e : CppExpr) (l : Loc),
        BigStepExprRVal s e (.ptr l) s' →
        l ≠ nullLoc →
        BigStepExpr s (.deref e) (.lval l) s'

    -- ── 二項演算 ──────────────────────────────────────
    -- 左から右へ評価。evalBinOp が none の場合は規則なし（stuck）。
    | E_BinOp : ∀ (s s1 s2 : State) (op : BinOp)
                  (e1 e2 : CppExpr) (v1 v2 v : RValue),
        BigStepExprRVal s  e1 v1 s1 →
        BigStepExprRVal s1 e2 v2 s2 →
        evalBinOp op v1 v2 = some v →
        BigStepExpr s (.binop op e1 e2) (.rval v) s2

    -- ── 純粋単項演算（neg / not / bitNot）────────────
    | E_PureUnOp : ∀ (s s' : State) (op : UnOp) (e : CppExpr)
                     (v v' : RValue),
        op = .neg ∨ op = .not ∨ op = .bitNot →
        BigStepExprRVal s e v s' →
        evalPureUnOp op v = some v' →
        BigStepExpr s (.unop op e) (.rval v') s'

    -- ── 前置インクリメント ++x ──────────────────────
    -- 結果は更新後の値。
    | E_PreInc : ∀ (s s1 s2 : State) (e : CppExpr) (l : Loc) (n : Int),
        BigStepExpr s e (.lval l) s1 →
        LValToRVal s1 (.lval l) (.int n) →
        s1.writeScalar l (.int (n + 1)) = .ok PUnit.unit s2 →
        BigStepExpr s (.unop .preinc e) (.rval (.int (n + 1))) s2

    -- ── 前置デクリメント --x ──────────────────────
    | E_PreDec : ∀ (s s1 s2 : State) (e : CppExpr) (l : Loc) (n : Int),
        BigStepExpr s e (.lval l) s1 →
        LValToRVal s1 (.lval l) (.int n) →
        s1.writeScalar l (.int (n - 1)) = .ok PUnit.unit s2 →
        BigStepExpr s (.unop .predec e) (.rval (.int (n - 1))) s2

    -- ── 後置インクリメント x++ ──────────────────────
    -- 結果は更新前の値。
    | E_PostInc : ∀ (s s1 s2 : State) (e : CppExpr) (l : Loc) (n : Int),
        BigStepExpr s e (.lval l) s1 →
        LValToRVal s1 (.lval l) (.int n) →
        s1.writeScalar l (.int (n + 1)) = .ok PUnit.unit s2 →
        BigStepExpr s (.unop .postinc e) (.rval (.int n)) s2

    -- ── 後置デクリメント x-- ──────────────────────
    | E_PostDec : ∀ (s s1 s2 : State) (e : CppExpr) (l : Loc) (n : Int),
        BigStepExpr s e (.lval l) s1 →
        LValToRVal s1 (.lval l) (.int n) →
        s1.writeScalar l (.int (n - 1)) = .ok PUnit.unit s2 →
        BigStepExpr s (.unop .postdec e) (.rval (.int n)) s2

    -- ── 単純代入 e1 = e2 ──────────────────────────
    -- e1 は lval（書き込み先）。e2 は rval（書き込む値）。
    -- lhs は未初期化でも良い（overwrite するから）。
    | E_SimpleAssign : ∀ (s s1 s2 s3 : State) (e1 e2 : CppExpr)
                         (l : Loc) (v : RValue),
        BigStepExpr s  e1 (.lval l) s1 →
        BigStepExprRVal s1 e2 v s2 →
        s2.writeScalar l v = .ok PUnit.unit s3 →
        BigStepExpr s (.assign .assign e1 e2) (.rval v) s3

    -- ── 複合代入 e1 op= e2（op ≠ assign）─────────
    -- lhs は初期化済みが必要（現在値を読むから）。
    | E_CompoundAssign : ∀ (s s1 s2 s3 : State) (op : AssignOp)
                           (e1 e2 : CppExpr) (l : Loc)
                           (v1 v2 v_new : RValue),
        op ≠ .assign →
        BigStepExpr s  e1 (.lval l) s1 →
        LValToRVal s1 (.lval l) v1 →  -- 現在値を読む
        BigStepExprRVal s1 e2 v2 s2 →
        evalAssignOp op v1 v2 = some v_new →
        s2.writeScalar l v_new = .ok PUnit.unit s3 →
        BigStepExpr s (.assign op e1 e2) (.rval v_new) s3

    -- ── 三項演算子 c ? e1 : e2 ───────────────────
    | E_TernaryTrue : ∀ (s s1 s2 : State) (c e1 e2 : CppExpr) (r : ExprResult),
        BigStepExprRVal s  c (.bool true) s1 →
        BigStepExpr s1 e1 r s2 →
        BigStepExpr s (.ternary c e1 e2) r s2

    | E_TernaryFalse : ∀ (s s1 s2 : State) (c e1 e2 : CppExpr) (r : ExprResult),
        BigStepExprRVal s  c (.bool false) s1 →
        BigStepExpr s1 e2 r s2 →
        BigStepExpr s (.ternary c e1 e2) r s2

    -- ── コンマ演算子 e1, e2 ────────────────────────
    -- e1 を評価（副作用のため）して捨て、e2 の結果を返す。
    | E_Comma : ∀ (s s1 s2 : State) (e1 e2 : CppExpr)
                  (r1 r : ExprResult),
        BigStepExpr s  e1 r1 s1 →
        BigStepExpr s1 e2 r  s2 →
        BigStepExpr s (.comma e1 e2) r s2

    -- ── キャスト（核断片の 3 種）─────────────────
    | E_CastIntToFloat : ∀ (s s' : State) (e : CppExpr) (n : Int),
        BigStepExprRVal s e (.int n) s' →
        BigStepExpr s (.cast CFloat e) (.rval (.float n.toFloat)) s'

    | E_CastFloatToInt : ∀ (s s' : State) (e : CppExpr) (f : Float),
        BigStepExprRVal s e (.float f) s' →
        BigStepExpr s (.cast CInt e) (.rval (.int f.toInt)) s'

    | E_CastIntToBool : ∀ (s s' : State) (e : CppExpr) (n : Int),
        BigStepExprRVal s e (.int n) s' →
        BigStepExpr s (.cast CBool e) (.rval (.bool (n ≠ 0))) s'

  /-
  BigStepExprRVal s e v s'

  s で e を評価し、lval-to-rval 変換まで適用して RValue v を得る。
  BigStepExpr + LValToRVal の合成。
  -/
  inductive BigStepExprRVal : State → CppExpr → RValue → State → Prop where
    | intro : ∀ (s s' : State) (e : CppExpr) (r : ExprResult) (v : RValue),
        BigStepExpr s e r s' →
        LValToRVal s' r v →
        BigStepExprRVal s e v s'

end

-- ──────────────────────────────────────────────
-- 文の big-step 関係
-- ──────────────────────────────────────────────

mutual

  /-
  BigStepStmt s st ctrl s'

  状態 s で文 st を実行すると制御結果 ctrl と新状態 s' が得られる。
  ctrl = .normal   : 次の文へ
  ctrl = .break_   : 最近傍のループ/switch を終了
  ctrl = .continue_: 最近傍のループの次のイテレーション
  ctrl = .return_ v: 関数から戻る（値 v で）
  -/
  inductive BigStepStmt : State → CppStmt → Control → State → Prop where

    -- ── 空文 ────────────────────────────────────────
    | S_Skip : ∀ (s : State),
        BigStepStmt s .skip .normal s

    -- ── 式文 ────────────────────────────────────────
    -- 式を評価して結果は捨てる。状態変化（副作用）だけが残る。
    | S_Expr : ∀ (s s' : State) (e : CppExpr) (r : ExprResult),
        BigStepExpr s e r s' →
        BigStepStmt s (.expr e) .normal s'

    -- ── ブロック ─────────────────────────────────────
    -- スコープ管理：enterScope → 本体 → exitScope。
    -- break/continue/return があっても必ず exitScope する。
    -- （= C++ のスタック変数の確実なデストラクト）
    | S_Block : ∀ (s s_in s_body s_out : State)
                  (ss : List CppStmt) (ctrl : Control)
                  (fr : Frame) (env' : Env),
        s_in = s.enterScope →
        BigStepStmts s_in ss ctrl s_body →
        Env.exitScope s_body.env = some (fr, env') →
        s_out = { s_body with
                  env   := env',
                  store := Store.killMany s_body.store fr.owned } →
        BigStepStmt s (.block ss) ctrl s_out

    -- ── 変数宣言 ─────────────────────────────────────
    -- (a) 初期化なし: 未初期化 cell を作る
    | S_DeclNone : ∀ (s s' : State) (d : VarDecl) (l : Loc),
        d.init = .none →
        s.declareStackObject d.name d.type
            (.scalar .void) (initialized := false)
          = .ok l s' →
        BigStepStmt s (.decl d) .normal s'

    -- (b) 直接初期化: 式を評価して初期化済み cell を作る
    | S_DeclDirect : ∀ (s s1 s2 : State) (d : VarDecl)
                       (e : CppExpr) (v : RValue) (l : Loc),
        d.init = .direct e →
        BigStepExprRVal s e v s1 →
        s1.declareStackObject d.name d.type
            (.scalar v) (initialized := true)
          = .ok l s2 →
        BigStepStmt s (.decl d) .normal s2

    -- ── if 文 ────────────────────────────────────────
    | S_IteTrue : ∀ (s s_c s' : State)
                    (c : CppExpr) (st1 st2 : CppStmt) (ctrl : Control),
        BigStepExprRVal s c (.bool true) s_c →
        BigStepStmt s_c st1 ctrl s' →
        BigStepStmt s (.ite c st1 st2) ctrl s'

    | S_IteFalse : ∀ (s s_c s' : State)
                     (c : CppExpr) (st1 st2 : CppStmt) (ctrl : Control),
        BigStepExprRVal s c (.bool false) s_c →
        BigStepStmt s_c st2 ctrl s' →
        BigStepStmt s (.ite c st1 st2) ctrl s'

    -- ── return 文 ─────────────────────────────────────
    | S_ReturnVoid : ∀ (s : State),
        BigStepStmt s (.return_ none) (.return_ .void) s

    | S_ReturnValue : ∀ (s s' : State) (e : CppExpr) (v : RValue),
        BigStepExprRVal s e v s' →
        BigStepStmt s (.return_ (some e)) (.return_ v) s'

    -- ── break / continue ──────────────────────────────
    | S_Break : ∀ (s : State),
        BigStepStmt s .break_ .break_ s

    | S_Continue : ∀ (s : State),
        BigStepStmt s .continue_ .continue_ s

  /-
  BigStepStmts s ss ctrl s'

  文リスト ss を先頭から順に実行する。
  途中で abrupt な control（break/continue/return）が起きたら
  残りの文は実行しない。
  -/
  inductive BigStepStmts : State → List CppStmt → Control → State → Prop where

    -- 空リストは正常終了
    | S_Nil : ∀ (s : State),
        BigStepStmts s [] .normal s

    -- 先頭が正常終了 → 残りを続ける
    | S_ConsNormal : ∀ (s s' s'' : State)
                       (st : CppStmt) (rest : List CppStmt) (ctrl : Control),
        BigStepStmt  s  st .normal s' →
        BigStepStmts s' rest ctrl s'' →
        BigStepStmts s (st :: rest) ctrl s''

    -- 先頭が abrupt → 残りをスキップして ctrl を伝搬
    | S_ConsAbrupt : ∀ (s s' : State)
                       (st : CppStmt) (rest : List CppStmt) (ctrl : Control),
        ctrl ≠ .normal →
        BigStepStmt s st ctrl s' →
        BigStepStmts s (st :: rest) ctrl s'

end

-- ============================================================
-- §4. 有用な導出補題
-- ============================================================

section DerivedLemmas

-- lval の変数は var x から得る
theorem bigStepExpr_var_lval
    (s : State) (x : Ident) (l : Loc)
    (h : s.locOf x = some l) :
    BigStepExpr s (.var x) (.lval l) s :=
  BigStepExpr.E_Var s x l h

-- rval として変数を読む（lval→rval 変換込み）
theorem bigStepExprRVal_var
    (s : State) (x : Ident) (l : Loc) (c : Cell) (v : RValue)
    (hloc : s.locOf x = some l)
    (hread : s.readCell l = some c)
    (halive : c.alive = true)
    (hinit : c.initialized = true)
    (hobj : c.object = .scalar v) :
    BigStepExprRVal s (.var x) v s :=
  BigStepExprRVal.intro s s (.var x) (.lval l) v
    (BigStepExpr.E_Var s x l hloc)
    (LValToRVal.ofLVal s l c v hread halive hinit hobj)

-- BigStepStmts は BigStepStmt の列
theorem bigStepStmts_singleton
    (s s' : State) (st : CppStmt) (ctrl : Control)
    (h : BigStepStmt s st ctrl s') :
    BigStepStmts s [st] ctrl s' := by
  cases h_ctrl : ctrl with
  | normal =>
      exact BigStepStmts.S_ConsNormal s s' s' st [] .normal
        (h_ctrl ▸ h) (BigStepStmts.S_Nil s')
  | break_ =>
      exact BigStepStmts.S_ConsAbrupt s s' st [] .break_
        (by decide) (h_ctrl ▸ h)
  | continue_ =>
      exact BigStepStmts.S_ConsAbrupt s s' st [] .continue_
        (by decide) (h_ctrl ▸ h)
  | return_ v =>
      exact BigStepStmts.S_ConsAbrupt s s' st [] (.return_ v)
        (by intro hh; cases hh) (h_ctrl ▸ h)

end DerivedLemmas

-- ============================================================
-- §5. 決定論性
--
-- big-step 関係は決定論的：同じ入力から最大 1 つの出力。
-- これが「evaluator が仕様に忠実」の基盤。
-- ============================================================

section Determinism

/-
LValToRVal の決定論性：
同じ ExprResult から得られる RValue は一意。
-/
theorem lvalToRVal_deterministic
    (s : State) (r : ExprResult) (v1 v2 : RValue)
    (h1 : LValToRVal s r v1) (h2 : LValToRVal s r v2) :
    v1 = v2 := by
  cases h1 with
  | ofRVal s v =>
      cases h2 with
      | ofRVal => rfl
  | ofLVal s l c v hread halive hinit hobj =>
      cases h2 with
      | ofLVal s l c' v' hread' halive' hinit' hobj' =>
          rw [hread] at hread'
          cases hread'
          rw [hobj] at hobj'
          cases hobj'
          rfl

/-
BigStepExpr の決定論性（主定理）

同じ式・同じ初期状態から評価が複数回成立したとき、
結果と最終状態は等しい。

証明は式の構造に対する帰納法。
-/
theorem bigStepExpr_deterministic
    (s : State) (e : CppExpr) (r1 r2 : ExprResult) (s1 s2 : State)
    (h1 : BigStepExpr s e r1 s1) (h2 : BigStepExpr s e r2 s2) :
    r1 = r2 ∧ s1 = s2 := by
  induction h1 generalizing r2 s2 with

  | E_Lit s lit =>
      cases h2; exact ⟨rfl, rfl⟩

  | E_Var s x l hloc =>
      cases h2 with
      | E_Var s x l' hloc' =>
          rw [hloc] at hloc'; cases hloc'; exact ⟨rfl, rfl⟩

  | E_AddrOf s s' e l he ih =>
      cases h2 with
      | E_AddrOf s s'' e l' he' =>
          have ⟨hr, hs⟩ := ih he'
          cases hr; cases hs
          exact ⟨rfl, rfl⟩

  | E_Deref s s' e l hrv hnn =>
      cases h2 with
      | E_Deref s s'' e l' hrv' hnn' =>
          -- BigStepExprRVal の決定論性が必要
          sorry

  | E_BinOp s s1 s2 op e1 e2 v1 v2 v hrv1 hrv2 heval ih1 ih2 =>
      cases h2 with
      | E_BinOp s s1' s2' op e1 e2 v1' v2' v' hrv1' hrv2' heval' =>
          sorry

  | E_PureUnOp s s' op e v v' hop hrv heval ih =>
      cases h2 with
      | E_PureUnOp s s'' op e v'' v''' hop' hrv' heval' =>
          sorry

  | E_PreInc s s1 s2 e l n he hlval hwrite ih =>
      cases h2 with
      | E_PreInc s s1' s2' e l' n' he' hlval' hwrite' =>
          sorry

  | E_PostInc s s1 s2 e l n he hlval hwrite ih =>
      cases h2 with
      | E_PostInc s s1' s2' e l' n' he' hlval' hwrite' =>
          sorry

  | E_PreDec s s1 s2 e l n he hlval hwrite ih =>
      cases h2 with
      | E_PreDec s s1' s2' e l' n' he' hlval' hwrite' =>
          sorry

  | E_PostDec s s1 s2 e l n he hlval hwrite ih =>
      cases h2 with
      | E_PostDec s s1' s2' e l' n' he' hlval' hwrite' =>
          sorry

  | E_SimpleAssign s s1 s2 s3 e1 e2 l v he1 hrv2 hwrite ih1 ih2 =>
      cases h2 with
      | E_SimpleAssign s s1' s2' s3' e1 e2 l' v' he1' hrv2' hwrite' =>
          sorry

  | E_CompoundAssign s s1 s2 s3 op e1 e2 l v1 v2 vn hneq he1 hlval hrv2 heval hwrite ih1 ih2 =>
      cases h2 with
      | E_CompoundAssign => sorry

  | E_TernaryTrue s s1 s2 c e1 e2 r hcond he ih1 ih2 =>
      cases h2 with
      | E_TernaryTrue s s1' s2' c e1 e2 r' hcond' he' =>
          sorry
      | E_TernaryFalse s s1' s2' c e1 e2 r' hcond' he' =>
          -- .bool true ≠ .bool false の矛盾
          sorry

  | E_TernaryFalse s s1 s2 c e1 e2 r hcond he ih1 ih2 =>
      cases h2 with
      | E_TernaryTrue => sorry
      | E_TernaryFalse => sorry

  | E_Comma s s1 s2 e1 e2 r1' r he1 he2 ih1 ih2 =>
      cases h2 with
      | E_Comma s s1' s2' e1 e2 r1'' r' he1' he2' =>
          sorry

  | E_CastIntToFloat s s' e n hrv ih =>
      cases h2 with
      | E_CastIntToFloat s s'' e n' hrv' => sorry

  | E_CastFloatToInt s s' e f hrv ih =>
      cases h2 with
      | E_CastFloatToInt s s'' e f' hrv' => sorry

  | E_CastIntToBool s s' e n hrv ih =>
      cases h2 with
      | E_CastIntToBool s s'' e n' hrv' => sorry

/- 注: sorry は全て同じ構造の補題に依存する。
   - BigStepExprRVal の決定論性（BigStepExpr 決定論性から導出）
   - writeScalar の関数性（同じ入力 → 同じ出力）
   - lvalToRVal_deterministic の活用
   Phase 5 で一括して証明する。
-/

/-
BigStepStmt の決定論性
-/
theorem bigStepStmt_deterministic
    (s : State) (st : CppStmt) (ctrl1 ctrl2 : Control) (s1 s2 : State)
    (h1 : BigStepStmt s st ctrl1 s1) (h2 : BigStepStmt s st ctrl2 s2) :
    ctrl1 = ctrl2 ∧ s1 = s2 := by
  sorry -- Phase 5: bigStepExpr_deterministic から導出

end Determinism

-- ============================================================
-- §6. 状態単調性（nextLoc は評価で単調増加する）
-- ============================================================

section Monotonicity

theorem bigStepExpr_nextLoc_mono
    (s s' : State) (e : CppExpr) (r : ExprResult)
    (h : BigStepExpr s e r s') :
    s.nextLoc ≤ s'.nextLoc := by
  induction h with
  | E_Lit => le_refl _
  | E_Var => le_refl _
  | E_AddrOf _ _ _ _ _ ih => exact ih
  | E_Deref _ _ _ _ hrv _ =>
      -- BigStepExprRVal の単調性が必要
      sorry
  | E_BinOp _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact Nat.le_trans ih1 ih2
  | E_PureUnOp _ _ _ _ _ _ _ _ _ ih => exact ih
  | E_PreInc s s1 s2 _ _ _ _ _ hwrite _ =>
      -- writeScalar は nextLoc を変えない
      sorry
  | E_PostInc s s1 s2 _ _ _ _ _ hwrite _ => sorry
  | E_PreDec s s1 s2 _ _ _ _ _ hwrite _ => sorry
  | E_PostDec s s1 s2 _ _ _ _ _ hwrite _ => sorry
  | E_SimpleAssign _ _ _ _ _ _ _ _ _ _ hwrite ih1 ih2 =>
      sorry
  | E_CompoundAssign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwrite ih1 ih2 =>
      sorry
  | E_TernaryTrue _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      sorry
  | E_TernaryFalse _ _ _ _ _ _ _ _ _ ih1 ih2 => sorry
  | E_Comma _ _ _ _ _ _ _ _ _ ih1 ih2 => exact Nat.le_trans ih1 ih2
  | E_CastIntToFloat _ _ _ _ _ ih => exact ih
  | E_CastFloatToInt _ _ _ _ _ ih => exact ih
  | E_CastIntToBool _ _ _ _ _ ih => exact ih

theorem bigStepStmt_nextLoc_mono
    (s s' : State) (st : CppStmt) (ctrl : Control)
    (h : BigStepStmt s st ctrl s') :
    s.nextLoc ≤ s'.nextLoc := by
  induction h with
  | S_Skip => le_refl _
  | S_Expr _ _ _ _ _ ih => exact ih
  | S_Block _ _ _ _ _ _ _ _ _ hstmts _ _ ih =>
      -- exitScope は nextLoc を変えない
      sorry
  | S_DeclNone s s' d l _ hdecl =>
      have := (declareStackObject_success_contract s s' d.name d.type
        (.scalar .void) false l (by
          convert hdecl using 2; simp)).2.2.2.2.1
      omega
  | S_DeclDirect s s1 s2 d e v l _ _ hdecl ih =>
      have hmono : s1.nextLoc ≤ s2.nextLoc := by
        have := (declareStackObject_success_contract s1 s2 d.name d.type
          (.scalar v) true l hdecl).2.2.2.2.1
        omega
      exact Nat.le_trans ih hmono
  | S_IteTrue _ _ _ _ _ _ _ _ _ ih => exact ih
  | S_IteFalse _ _ _ _ _ _ _ _ _ ih => exact ih
  | S_ReturnVoid => le_refl _
  | S_ReturnValue _ _ _ _ _ ih => exact ih
  | S_Break => le_refl _
  | S_Continue => le_refl _

end Monotonicity

-- ============================================================
-- §7. 型保存の宣言（Phase 5 で証明）
-- ============================================================

section TypePreservation

/-
式の型保存定理：
型付き・安全な式の評価結果は元の型を持つ。

「WellTyped かつ Safe なら評価が詰まらず型を保つ」という主張。
これが Phase 5 の中心定理の一つ。
-/
theorem bigStepExpr_type_preservation
    (Γ : TyEnv) (stbl : StructTable) (s s' : State)
    (e : CppExpr) (τ : CppType) (r : ExprResult)
    (htyp   : HasType Γ stbl e τ)
    (hsafe  : SafeExpr Γ stbl s e)
    (hstate : TypedState Γ s)
    (heval  : BigStepExpr s e r s') :
    -- rval なら RValueHasType
    (∀ v, r = .rval v → RValueHasType v τ) ∧
    -- lval なら LValueHasType（型付き場所）
    (∀ l, r = .lval l → LValueHasType s' l τ) := by
  sorry -- Phase 5 で証明

/-
文の型保存定理（state 整合の保持）：
WF_Typed_Safe な状態から始めた文の実行は、
TypedState を保つ。
-/
theorem bigStepStmt_state_preservation
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s s' : State) (st : CppStmt) (ctrl : Control)
    (h    : WF_Typed_Safe Γ stbl retTy s st)
    (heval : BigStepStmt s st ctrl s') :
    TypedState Γ s' ∧ s'.WF := by
  sorry -- Phase 5 で証明

/-
no-stuck 定理（核断片版）：
WF_Typed_Safe な状態では、核断片の文は必ず評価が進む。
（= 型と安全性が揃っていれば stuck にならない）
-/
theorem bigStepStmt_no_stuck
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s : State) (st : CppStmt)
    (h : WF_Typed_Safe Γ stbl retTy s st) :
    ∃ ctrl s', BigStepStmt s st ctrl s' := by
  sorry -- Phase 5 で証明（核断片のみ）

end TypePreservation

-- ============================================================
-- §8. 使用例（サニティチェック）
-- ============================================================

section Examples

-- 例 1: リテラル 42 の評価
example : BigStepExpr State.empty (.lit (.int 42)) (.rval (.int 42)) State.empty :=
  BigStepExpr.E_Lit State.empty (.int 42)

-- 例 2: skip 文の評価
example : BigStepStmt State.empty .skip .normal State.empty :=
  BigStepStmt.S_Skip State.empty

-- 例 3: return 42 の評価
example : BigStepStmt State.empty
    (.return_ (some (.lit (.int 42))))
    (.return_ (.int 42))
    State.empty := by
  apply BigStepStmt.S_ReturnValue
  apply BigStepExprRVal.intro
  · exact BigStepExpr.E_Lit _ _
  · exact LValToRVal.ofRVal _ _

-- 例 4: 1 + 2 = 3 の評価
example : BigStepExpr State.empty
    (.binop .add (.lit (.int 1)) (.lit (.int 2)))
    (.rval (.int 3))
    State.empty := by
  apply BigStepExpr.E_BinOp
  · exact BigStepExprRVal.intro _ _ _ _ _ (BigStepExpr.E_Lit _ _) (LValToRVal.ofRVal _ _)
  · exact BigStepExprRVal.intro _ _ _ _ _ (BigStepExpr.E_Lit _ _) (LValToRVal.ofRVal _ _)
  · rfl

-- 例 5: if (true) { return 1; } else { return 2; }  →  return 1
example : BigStepStmt State.empty
    (.ite (.lit (.bool true))
          (.return_ (some (.lit (.int 1))))
          (.return_ (some (.lit (.int 2)))))
    (.return_ (.int 1))
    State.empty := by
  apply BigStepStmt.S_IteTrue
  · exact BigStepExprRVal.intro _ _ _ _ _ (BigStepExpr.E_Lit _ _) (LValToRVal.ofRVal _ _)
  · apply BigStepStmt.S_ReturnValue
    exact BigStepExprRVal.intro _ _ _ _ _ (BigStepExpr.E_Lit _ _) (LValToRVal.ofRVal _ _)

-- 例 6: evalBinOp のサニティチェック
#eval evalBinOp .add (.int 3) (.int 4)   -- some (.int 7)
#eval evalBinOp .div (.int 6) (.int 0)   -- none（0除算 = stuck）
#eval evalBinOp .lt  (.int 3) (.int 5)   -- some (.bool true)
#eval evalBinOp .and (.bool true) (.bool false) -- some (.bool false)

-- 例 7: interpretLiteral
#eval interpretLiteral (.int 42)          -- RValue.int 42
#eval interpretLiteral .null              -- RValue.ptr 0 (= nullLoc)

end Examples

end Cpp
