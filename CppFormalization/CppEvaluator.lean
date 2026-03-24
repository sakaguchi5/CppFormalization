import CppFormalization.CppState
import CppFormalization.CppState_Contracts
import CppFormalization.Phase2.CppTyping
import CppFormalization.Phase2_5.CppSafety
import CppFormalization.Phase3.CppBigStep

namespace Cpp

/-
Phase 4: Fuel-based Evaluator

設計原則：
  1. fuel = 0 なら常に .timeout（停止性問題を回避）
  2. fuel の消費は「ループの 1 イテレーション」と「関数呼び出し 1 回」のみ
     （式のサブ式は fuel を消費しない）
  3. while / for をここで初めて実装する（Phase 3 では意図的に除外）
  4. 評価器は Phase 3 の BigStep 関係の「実行可能な近似」である
  5. timeout と error は明確に分離：
       timeout → 「fuel が足りなかった」（意味論的失敗ではない）
       error   → 「実行時エラー」（BigStep に対応する規則なし）

核断片（Phase 3 同等）に while / for / while-do を追加：
  式: lit / var / addrOf / deref / binop / unop / assign /
      ternary / comma / cast
  文: skip / expr / block / decl / ite / return / break / continue /
      while / doWhile / for

関数呼び出しは Phase 5 以降で扱う（evaluator の複雑度を段階的に上げる）。
-/

-- ============================================================
-- §1. EvalResult の束縛演算子（do 記法の基盤）
-- ============================================================

/-
EvalResult はすでに CppState.lean で定義されているが、
evaluator 内での連鎖を読みやすくするため do 記法を有効にする。
-/

instance : Monad (EvalResult) where
  pure a := fun s => .ok a s   -- ← EvalResult は State を暗黙引数に取らないので直接は書けない
  bind  := EvalResult.bind

-- 注: EvalResult α は State を外から受け取る設計なので、
--     実際の連鎖は EvalResult.bind を直接使う形式で書く。

-- 状態つきの「純粋に成功する」ヘルパー
@[inline]
def ok' {α : Type} (a : α) (s : State) : EvalResult α := .ok a s

-- EvalResult から RValue に変換（lval→rval 変換込み）
@[inline]
def toRVal (r : ExprResult) (s : State) : EvalResult RValue :=
  ExprResult.toRValue r s

-- EvalResult から Loc に変換
@[inline]
def toLoc (r : ExprResult) (s : State) : EvalResult Loc :=
  ExprResult.toLoc r s

-- ============================================================
-- §2. 式の評価器
-- ============================================================

/-
evalExpr : Nat → State → CppExpr → EvalResult ExprResult

燃料 fuel のもとで式 e を評価する。
- fuel = 0 → .timeout s
- 正常評価 → .ok (ExprResult) s'
- 実行時エラー → .error e s'

設計：
  evalExpr と evalStmt は相互再帰だが、
  Lean の termination checker のために fuel に対する
  structural recursion として定義する。
-/

mutual

  /-- 式評価器 -/
  def evalExpr (fuel : Nat) (s : State) (e : CppExpr)
      : EvalResult ExprResult :=
    match fuel with
    | 0     => .timeout s
    | n + 1 =>
      match e with

      -- ── リテラル ─────────────────────────────────────────
      | .lit lit =>
          .ok (.rval (interpretLiteral lit)) s

      -- ── 変数 ─────────────────────────────────────────────
      -- 変数は lval（場所）を返す。読み取りは呼び出し元が行う。
      | .var x =>
          match s.locOf x with
          | none   => .error (.unboundVar x) s
          | some l => .ok (.lval l) s

      -- ── アドレス取得  &e ─────────────────────────────────
      | .addrOf e =>
          (evalExpr n s e).bind fun r s1 =>
          match r with
          | .rval _  => .error .notAssignable s1
          | .lval l  => .ok (.rval (.ptr l)) s1

      -- ── デリファレンス  *e ────────────────────────────────
      | .deref e =>
          (evalExpr n s e).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .ptr l =>
              if l = nullLoc
              then .error .nullDeref s2
              else .ok (.lval l) s2
          | _ => .error .typeMismatch s2

      -- ── 二項演算 ─────────────────────────────────────────
      | .binop op e1 e2 =>
          (evalExpr n s e1).bind fun r1 s1 =>
          (toRVal r1 s1).bind fun v1 s2 =>
          (evalExpr n s2 e2).bind fun r2 s3 =>
          (toRVal r2 s3).bind fun v2 s4 =>
          match evalBinOp op v1 v2 with
          | none   => .error .typeMismatch s4
          | some v => .ok (.rval v) s4

      -- ── 純粋単項演算（neg / not / bitNot）──────────────
      | .unop op e =>
          match op with
          | .neg | .not | .bitNot =>
              (evalExpr n s e).bind fun r s1 =>
              (toRVal r s1).bind fun v s2 =>
              match evalPureUnOp op v with
              | none    => .error .typeMismatch s2
              | some v' => .ok (.rval v') s2

          -- ── 前置インクリメント  ++x ─────────────────────
          | .preinc =>
              (evalExpr n s e).bind fun r s1 =>
              (toLoc r s1).bind fun l s2 =>
              (toRVal (.lval l) s2).bind fun v s3 =>
              match v with
              | .int i =>
                  (s3.writeScalar l (.int (i + 1))).bind fun _ s4 =>
                  .ok (.rval (.int (i + 1))) s4
              | _ => .error .typeMismatch s3

          -- ── 前置デクリメント  --x ─────────────────────
          | .predec =>
              (evalExpr n s e).bind fun r s1 =>
              (toLoc r s1).bind fun l s2 =>
              (toRVal (.lval l) s2).bind fun v s3 =>
              match v with
              | .int i =>
                  (s3.writeScalar l (.int (i - 1))).bind fun _ s4 =>
                  .ok (.rval (.int (i - 1))) s4
              | _ => .error .typeMismatch s3

          -- ── 後置インクリメント  x++ ────────────────────
          | .postinc =>
              (evalExpr n s e).bind fun r s1 =>
              (toLoc r s1).bind fun l s2 =>
              (toRVal (.lval l) s2).bind fun v s3 =>
              match v with
              | .int i =>
                  (s3.writeScalar l (.int (i + 1))).bind fun _ s4 =>
                  .ok (.rval (.int i)) s4     -- 後置: 元の値を返す
              | _ => .error .typeMismatch s3

          -- ── 後置デクリメント  x-- ────────────────────
          | .postdec =>
              (evalExpr n s e).bind fun r s1 =>
              (toLoc r s1).bind fun l s2 =>
              (toRVal (.lval l) s2).bind fun v s3 =>
              match v with
              | .int i =>
                  (s3.writeScalar l (.int (i - 1))).bind fun _ s4 =>
                  .ok (.rval (.int i)) s4     -- 後置: 元の値を返す
              | _ => .error .typeMismatch s3

      -- ── 代入式 ───────────────────────────────────────────
      | .assign op lhs rhs =>
          (evalExpr n s lhs).bind fun r_lhs s1 =>
          (toLoc r_lhs s1).bind fun l s2 =>
          (evalExpr n s2 rhs).bind fun r_rhs s3 =>
          (toRVal r_rhs s3).bind fun v_rhs s4 =>
          -- 複合代入は現在値も読む
          let getNewVal : EvalResult RValue :=
            if op = .assign
            then .ok v_rhs s4
            else
              (toRVal (.lval l) s4).bind fun v_lhs s5 =>
              match evalAssignOp op v_lhs v_rhs with
              | none       => .error .typeMismatch s5
              | some v_new => .ok v_new s5
          getNewVal.bind fun v_new s5 =>
          (s5.writeScalar l v_new).bind fun _ s6 =>
          .ok (.rval v_new) s6

      -- ── 三項演算子  c ? e1 : e2 ─────────────────────────
      | .ternary cond e1 e2 =>
          (evalExpr n s cond).bind fun r_c s1 =>
          (toRVal r_c s1).bind fun v_c s2 =>
          match v_c with
          | .bool true  => evalExpr n s2 e1
          | .bool false => evalExpr n s2 e2
          | _           => .error .typeMismatch s2

      -- ── コンマ演算子  e1, e2 ─────────────────────────────
      | .comma e1 e2 =>
          (evalExpr n s e1).bind fun _ s1 =>
          evalExpr n s1 e2

      -- ── キャスト ─────────────────────────────────────────
      | .cast τ inner =>
          (evalExpr n s inner).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match τ, v with
          | CFloat, .int i   => .ok (.rval (.float i.toFloat)) s2
          | CInt,   .float f => .ok (.rval (.int f.toInt)) s2
          | CBool,  .int i   => .ok (.rval (.bool (i ≠ 0))) s2
          | CInt,   .int _   => .ok (.rval v) s2   -- identity cast
          | CFloat, .float _ => .ok (.rval v) s2
          | CBool,  .bool _  => .ok (.rval v) s2
          | _, _ => .error .invalidCast s2

      -- ── sizeof ───────────────────────────────────────────
      -- 理想化: 全型のサイズをコンパイル時定数 1 として扱う
      | .sizeofType _ => .ok (.rval (.uint 1)) s
      | .sizeofExpr _ => .ok (.rval (.uint 1)) s

      -- ── new / delete ────────────────────────────────────
      | .new_ ty initOpt =>
          let initObj : EvalResult Object :=
            match initOpt with
            | none   =>
                .ok (.scalar .void) s   -- 未初期化
            | some e =>
                (evalExpr n s e).bind fun r s1 =>
                (toRVal r s1).bind fun v s2 =>
                .ok (.scalar v) s2
          initObj.bind fun obj s1 =>
          let initialized := initOpt.isSome
          (s1.allocHeapObject ty obj initialized).bind fun pv s2 =>
          .ok (.rval pv) s2

      | .delete_ e =>
          (evalExpr n s e).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .ptr l =>
              if l = nullLoc
              then .ok (.rval .void) s2   -- delete nullptr は no-op
              else
                match s2.modifyCell? l Cell.kill with
                | none    => .error (.useAfterFree l) s2
                | some s3 => .ok (.rval .void) s3
          | _ => .error .typeMismatch s2

      -- ── member / arrow / index (核断片で扱う範囲のみ) ──
      | .member e field =>
          (evalExpr n s e).bind fun r s1 =>
          (toLoc r s1).bind fun l s2 =>
          match s2.readCell l with
          | none   => .error (.invalidLoc l) s2
          | some c =>
              if !c.alive then .error (.useAfterFree l) s2
              else
                match c.object.fieldLoc? field with
                | none    => .error (.missingField field) s2
                | some l' => .ok (.lval l') s2

      | .arrow e field =>
          (evalExpr n s e).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .ptr l =>
              if l = nullLoc then .error .nullDeref s2
              else
                match s2.readCell l with
                | none   => .error (.invalidLoc l) s2
                | some c =>
                    if !c.alive then .error (.useAfterFree l) s2
                    else
                      match c.object.fieldLoc? field with
                      | none    => .error (.missingField field) s2
                      | some l' => .ok (.lval l') s2
          | _ => .error .typeMismatch s2

      | .index e1 e2 =>
          (evalExpr n s e1).bind fun r1 s1 =>
          (toLoc r1 s1).bind fun l_arr s2 =>
          (evalExpr n s2 e2).bind fun r2 s3 =>
          (toRVal r2 s3).bind fun v_idx s4 =>
          match v_idx with
          | .int i =>
              if i < 0 then .error .outOfBounds s4
              else
                match s4.readCell l_arr with
                | none   => .error (.invalidLoc l_arr) s4
                | some c =>
                    if !c.alive then .error (.useAfterFree l_arr) s4
                    else
                      match c.object.indexLoc? i.toNat with
                      | none    => .error .outOfBounds s4
                      | some l' => .ok (.lval l') s4
          | _ => .error .typeMismatch s4

      -- ── 未サポート ───────────────────────────────────────
      | .call _ _ =>
          -- 関数呼び出しは Phase 5 以降
          .error (.unsupported "call") s
      | .sizeofExpr _ =>
          .ok (.rval (.uint 1)) s

  /-- 文評価器 -/
  def evalStmt (fuel : Nat) (s : State) (st : CppStmt)
      : StmtResult :=
    match fuel with
    | 0     => .timeout s
    | n + 1 =>
      match st with

      -- ── 空文 ─────────────────────────────────────────────
      | .skip => .ok .normal s

      -- ── 式文 ─────────────────────────────────────────────
      | .expr e =>
          (evalExpr n s e).bind fun _ s1 =>
          .ok .normal s1

      -- ── ブロック ─────────────────────────────────────────
      -- enterScope → 本体 → exitScope（abrupt でも必ず実行）
      | .block ss =>
          let s_in := s.enterScope
          (evalStmts n s_in ss).bind fun ctrl s_body =>
          (s_body.exitScope).bind fun _ s_out =>
          .ok ctrl s_out

      -- ── 変数宣言 ─────────────────────────────────────────
      | .decl d =>
          match d.init with
          | .none =>
              -- 未初期化宣言
              (s.declareStackObject d.name d.type
                (.scalar .void) (initialized := false)).bind fun _ s1 =>
              .ok .normal s1
          | .direct e =>
              (evalExpr n s e).bind fun r s1 =>
              (toRVal r s1).bind fun v s2 =>
              (s2.declareStackObject d.name d.type
                (.scalar v) (initialized := true)).bind fun _ s3 =>
              .ok .normal s3
          | .list es =>
              -- list 初期化はシンプルな版：最初の要素だけ使う（理想化）
              match es with
              | [] =>
                  (s.declareStackObject d.name d.type
                    (.scalar .void) (initialized := false)).bind fun _ s1 =>
                  .ok .normal s1
              | e :: _ =>
                  (evalExpr n s e).bind fun r s1 =>
                  (toRVal r s1).bind fun v s2 =>
                  (s2.declareStackObject d.name d.type
                    (.scalar v) (initialized := true)).bind fun _ s3 =>
                  .ok .normal s3

      -- ── if 文 ─────────────────────────────────────────────
      | .ite cond thn els =>
          (evalExpr n s cond).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .bool true  => evalStmt n s2 thn
          | .bool false => evalStmt n s2 els
          | _           => .error .typeMismatch s2

      -- ── while 文 ─────────────────────────────────────────
      -- fuel を 1 消費するのは「ループの 1 イテレーション」
      -- これが停止性への態度の明示
      | .while_ cond body =>
          (evalExpr n s cond).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .bool false => .ok .normal s2   -- ループ終了
          | .bool true  =>
              (evalStmt n s2 body).bind fun ctrl s3 =>
              match ctrl with
              | .break_    => .ok .normal s3   -- break でループ脱出
              | .continue_ => evalStmt n s3 (.while_ cond body)  -- 次のイテレーション
              | .return_ v => .ok (.return_ v) s3   -- return を伝搬
              | .normal    => evalStmt n s3 (.while_ cond body)  -- 継続
          | _ => .error .typeMismatch s2

      -- ── do-while 文 ───────────────────────────────────────
      | .doWhile body cond =>
          (evalStmt n s body).bind fun ctrl s1 =>
          match ctrl with
          | .break_    => .ok .normal s1
          | .return_ v => .ok (.return_ v) s1
          | .continue_ | .normal =>
              (evalExpr n s1 cond).bind fun r s2 =>
              (toRVal r s2).bind fun v s3 =>
              match v with
              | .bool false => .ok .normal s3
              | .bool true  => evalStmt n s3 (.doWhile body cond)
              | _           => .error .typeMismatch s3

      -- ── for 文 ───────────────────────────────────────────
      -- for(init; cond; step) body
      -- ブロックとしてスコープを作る
      | .for_ init cond step body =>
          let s_in := s.enterScope
          -- init を実行
          let initResult : StmtResult :=
            match init with
            | .none   => .ok .normal s_in
            | .expr e =>
                (evalExpr n s_in e).bind fun _ s1 =>
                .ok .normal s1
            | .decl d => evalStmt n s_in (.decl d)
          initResult.bind fun _ s1 =>
          -- for のループ本体
          let rec forLoop (fuel' : Nat) (s_cur : State) : StmtResult :=
            match fuel' with
            | 0 => .timeout s_cur
            | m + 1 =>
                -- 条件チェック
                let condResult : EvalResult Bool :=
                  match cond with
                  | none   => .ok true s_cur   -- 条件なし = 常に true
                  | some e =>
                      (evalExpr n s_cur e).bind fun r s2 =>
                      (toRVal r s2).bind fun v s3 =>
                      match v with
                      | .bool b => .ok b s3
                      | _       => .error .typeMismatch s3
                condResult.bind fun b s2 =>
                if !b
                then .ok .normal s2
                else
                  -- body 実行
                  (evalStmt n s2 body).bind fun ctrl s3 =>
                  match ctrl with
                  | .break_    => .ok .normal s3
                  | .return_ v => .ok (.return_ v) s3
                  | .continue_ | .normal =>
                      -- step 実行
                      let stepResult : StmtResult :=
                        match step with
                        | none   => .ok .normal s3
                        | some e =>
                            (evalExpr n s3 e).bind fun _ s4 =>
                            .ok .normal s4
                      stepResult.bind fun _ s4 =>
                      forLoop m s4
          -- fuel をループに渡す（外側の n を使う）
          (forLoop n s1).bind fun ctrl s2 =>
          (s2.exitScope).bind fun _ s3 =>
          .ok ctrl s3

      -- ── range-based for（未サポート）───────────────────
      | .forRange _ _ _ _ =>
          .error (.unsupported "forRange") s

      -- ── return 文 ────────────────────────────────────────
      | .return_ none =>
          .ok (.return_ .void) s

      | .return_ (some e) =>
          (evalExpr n s e).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          .ok (.return_ v) s2

      -- ── break / continue ─────────────────────────────────
      | .break_    => .ok .break_ s
      | .continue_ => .ok .continue_ s

      -- ── switch 文 ───────────────────────────────────────
      | .switch_ e cases =>
          (evalExpr n s e).bind fun r s1 =>
          (toRVal r s1).bind fun v s2 =>
          match v with
          | .int i =>
              -- 一致する case を探す
              let rec findCase : List SwitchCase → StmtResult
                | [] => .ok .normal s2   -- どの case にもマッチしない
                | .case_ (.int ci) body :: rest =>
                    if ci = i
                    then evalStmts n s2 body
                    else findCase rest
                | .default_ body :: _ => evalStmts n s2 body
                | _ :: rest => findCase rest
              -- break を normal に変換（switch を脱出）
              (findCase cases).bind fun ctrl s3 =>
              match ctrl with
              | .break_ => .ok .normal s3
              | other   => .ok other s3
          | _ => .error .typeMismatch s2

  /-- 文リストの評価器 -/
  def evalStmts (fuel : Nat) (s : State) (ss : List CppStmt)
      : StmtResult :=
    match fuel with
    | 0 => .timeout s
    | n + 1 =>
      match ss with
      | [] => .ok .normal s
      | st :: rest =>
          (evalStmt n s st).bind fun ctrl s1 =>
          match ctrl with
          | .normal => evalStmts n s1 rest  -- 継続
          | abrupt  => .ok abrupt s1        -- abrupt は残りをスキップ

end

-- ============================================================
-- §3. Fuel 単調性
--
-- 「少ない fuel で成功したなら、多い fuel でも同じ結果」
-- これが timeout の性質の核心。
-- ============================================================

section FuelMonotonicity

/-
fuel 単調性の主定理：
  evalExpr n s e = .ok r s'  →  evalExpr (n + k) s e = .ok r s'
  evalStmt n s st = .ok c s' →  evalStmt (n + k) s st = .ok c s'

証明は fuel と式の構造に対する相互帰納法。
-/

-- まず補題：fuel を 1 増やしても ok は ok のまま
theorem evalExpr_fuel_mono_succ
    (s s' : State) (e : CppExpr) (r : ExprResult) (n : Nat)
    (h : evalExpr n s e = .ok r s') :
    evalExpr (n + 1) s e = .ok r s' := by
  sorry -- Phase 5 で証明（式の構造に対する帰納法）

theorem evalStmt_fuel_mono_succ
    (s s' : State) (st : CppStmt) (ctrl : Control) (n : Nat)
    (h : evalStmt n s st = .ok ctrl s') :
    evalStmt (n + 1) s st = .ok ctrl s' := by
  sorry -- Phase 5 で証明

-- 一般版：任意の k について
theorem evalExpr_fuel_mono
    (s s' : State) (e : CppExpr) (r : ExprResult) (n k : Nat)
    (h : evalExpr n s e = .ok r s') :
    evalExpr (n + k) s e = .ok r s' := by
  induction k with
  | zero      => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact evalExpr_fuel_mono_succ s s' e r (n + k) ih

theorem evalStmt_fuel_mono
    (s s' : State) (st : CppStmt) (ctrl : Control) (n k : Nat)
    (h : evalStmt n s st = .ok ctrl s') :
    evalStmt (n + k) s st = .ok ctrl s' := by
  induction k with
  | zero      => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact evalStmt_fuel_mono_succ s s' st ctrl (n + k) ih

-- timeout は fuel を増やすと消える可能性がある
-- （「有限実行が存在するなら十分な fuel で timeout は消える」は completeness から）
theorem evalExpr_timeout_implies_zero_or_recurse
    (s : State) (e : CppExpr) (n : Nat)
    (h : evalExpr n s e = .timeout s) :
    n = 0 ∨ ∃ n', n = n' + 1 := by
  cases n with
  | zero      => exact Or.inl rfl
  | succ n'   => exact Or.inr ⟨n', rfl⟩

end FuelMonotonicity

-- ============================================================
-- §4. Timeout と意味論的失敗の分離
-- ============================================================

section TimeoutSeparation

/-
主張: timeout は EvalError とは異なる出力コンストラクタである。
これは型の定義から自明だが、明示的に補題として書いておく。
-/

theorem timeout_ne_ok
    {α : Type} (s s' : State) (a : α) :
    (EvalResult.timeout s : EvalResult α) ≠ .ok a s' := by
  intro h; cases h

theorem timeout_ne_error
    {α : Type} (s s' : State) (e : EvalError) :
    (EvalResult.timeout s : EvalResult α) ≠ .error e s' := by
  intro h; cases h

/-
Timeout 分離定理：
evalStmt が .timeout を返した場合、
それは「意味論的失敗」(EvalError) が起きたことを意味しない。
-/
theorem timeout_not_semantic_failure
    (s : State) (st : CppStmt) (n : Nat)
    (h : evalStmt n s st = .timeout s) :
    ¬ ∃ (e : EvalError) (s' : State), evalStmt n s st = .error e s' := by
  intro ⟨e, s', hcontra⟩
  rw [h] at hcontra
  exact timeout_ne_error s s' e hcontra

/-
fuel = 0 は常に timeout：
-/
@[simp]
theorem evalExpr_zero (s : State) (e : CppExpr) :
    evalExpr 0 s e = .timeout s := by simp [evalExpr]

@[simp]
theorem evalStmt_zero (s : State) (st : CppStmt) :
    evalStmt 0 s st = .timeout s := by simp [evalStmt]

end TimeoutSeparation

-- ============================================================
-- §5. 健全性（Soundness）：evaluator → BigStep
--
-- 「evaluator が ok r s' を返したなら、
--   BigStep 関係  s ⊢ e ⇓ (r, s')  が成立する」
-- ============================================================

section Soundness

/-
式の評価器の健全性
-/
theorem evalExpr_sound
    (n : Nat) (s s' : State) (e : CppExpr) (r : ExprResult)
    (h : evalExpr n s e = .ok r s') :
    BigStepExpr s e r s' := by
  sorry
  /-
  証明の戦略：
    n と e の両方に対する相互帰納法。
    各ケースで evalExpr の定義を展開し、
    対応する BigStepExpr コンストラクタを適用する。

    例：E_Lit のケース
      h : evalExpr (n+1) s (.lit lit) = .ok (.rval (interpretLiteral lit)) s
      → simp [evalExpr] at h → h が .ok rfl → apply BigStepExpr.E_Lit

    例：E_BinOp のケース
      h : evalExpr (n+1) s (.binop op e1 e2) = .ok (.rval v) s4
      → bind の展開 → ih1 : BigStepExprRVal s e1 v1 s2
                     → ih2 : BigStepExprRVal s2 e2 v2 s3
      → evalBinOp op v1 v2 = some v
      → apply BigStepExpr.E_BinOp
  -/

-- BigStepExprRVal の健全性（evalExpr + toRVal の合成）
theorem evalExprRVal_sound
    (n : Nat) (s s' : State) (e : CppExpr) (v : RValue)
    (hr : evalExpr n s e = .ok (.rval v) s') :
    BigStepExprRVal s e v s' := by
  sorry

/-
文の評価器の健全性
-/
theorem evalStmt_sound
    (n : Nat) (s s' : State) (st : CppStmt) (ctrl : Control)
    (h : evalStmt n s st = .ok ctrl s') :
    BigStepStmt s st ctrl s' := by
  sorry

end Soundness

-- ============================================================
-- §6. 完全性（Completeness）：BigStep → evaluator
--
-- 「BigStep 関係が成立するなら、
--   十分大きい fuel で evaluator も ok を返す」
-- ============================================================

section Completeness

/-
式の評価器の完全性
-/
theorem evalExpr_complete
    (s s' : State) (e : CppExpr) (r : ExprResult)
    (h : BigStepExpr s e r s') :
    ∃ n : Nat, evalExpr n s e = .ok r s' := by
  sorry
  /-
  証明の戦略：
    BigStepExpr の帰納法。
    各ケースで、サブ式の帰納仮定から fuel を集め
    max を取ることで十分な fuel を構成する。

    例：E_Lit
      → ∃ n, n = 1 が証人（evalExpr 1 s (.lit lit) = .ok ...)

    例：E_BinOp
      ih1 : ∃ n1, evalExpr n1 s e1 = .ok (rval v1) s2
      ih2 : ∃ n2, evalExpr n2 s2 e2 = .ok (rval v2) s3
      → n = max n1 n2 + 1 が証人
      → fuel_mono で両方を n まで引き上げて証明
  -/

/-
文の評価器の完全性
-/
theorem evalStmt_complete
    (s s' : State) (st : CppStmt) (ctrl : Control)
    (h : BigStepStmt s st ctrl s') :
    ∃ n : Nat, evalStmt n s st = .ok ctrl s' := by
  sorry

/-
diverge 分離定理：
BigStep 関係が成立するなら（= 有限実行が存在するなら）、
十分大きい fuel では timeout は返さない。
-/
theorem noTimeout_if_bigStep
    (s s' : State) (st : CppStmt) (ctrl : Control)
    (hbs : BigStepStmt s st ctrl s') :
    ∀ n : Nat, evalStmt n s st = .timeout s →
      ∃ m : Nat, n < m ∧ evalStmt m s st = .ok ctrl s' := by
  intro n htimeout
  obtain ⟨fuel, hfuel⟩ := evalStmt_complete s s' st ctrl hbs
  refine ⟨fuel, ?_, hfuel⟩
  by_contra hle
  push_neg at hle
  -- n ≥ fuel のとき fuel_mono より evalStmt n s st ≠ timeout だが矛盾
  have hmono := evalStmt_fuel_mono s s' st ctrl fuel (n - fuel)
    (by simpa using hfuel)
  simp [Nat.add_sub_cancel' hle] at hmono
  rw [hmono] at htimeout
  exact timeout_ne_ok s s' ctrl htimeout

end Completeness

-- ============================================================
-- §7. エラー分類（Error Classification）
-- ============================================================

section ErrorClassification

/-
evaluator が EvalError を返すとき、それが何に起因するかを分類する。

このセクションが「逆説的にエラーが出ることは
数学範囲以外の要因である（あるいは前提違反）」の形式化。
-/

-- EvalError の分類：どのカテゴリに属するか
def EvalError.category : EvalError → ErrorKind
  | .unboundVar _       => .unboundVar       -- 静的整形で防げる
  | .uninitializedRead _ => .uninitRead      -- NoUninit で防げる
  | .notAssignable      => .badAssign        -- 静的整形で防げる
  | .nullDeref          => .nullDeref        -- NoUB で防げる
  | .outOfBounds        => .outOfBounds      -- NoUB で防げる
  | .useAfterFree _     => .useAfterFree     -- NoUB で防げる
  | .invalidCast        => .invalidCast      -- NoUB で防げる
  | .invalidLoc _       => .useAfterFree     -- 実質 useAfterFree
  | .typeMismatch       => .typeError        -- 型システムで防げる
  | .aggregateRValue    => .typeError        -- 型システムで防げる
  | .missingField _     => .typeError        -- 型システムで防げる
  | .arityMismatch _ _  => .typeError        -- 型システムで防げる
  | .scopeUnderflow     => .typeError        -- 静的整形で防げる
  | .unsupported _      => .environmental    -- 未実装は環境起因

/-
主定理（の宣言）：
WF_Typed_Safe な前提のもとでは、
evaluator は UB 起因のエラーを返さない。

Phase 5 で完全な証明を行う。
-/
theorem evalStmt_no_ub_error
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s : State) (st : CppStmt) (n : Nat)
    (h : WF_Typed_Safe Γ stbl retTy s st) :
    ∀ e s', evalStmt n s st = .error e s' →
      ¬ ErrorKind.isUB (e.category) := by
  sorry -- Phase 5 で証明（evaluator の健全性 + Phase 2.5 の安全性述語）

/-
逆説的エラー分類定理：
WF_Typed_Safe な前提のもとで評価器がエラーを返したなら、
そのエラーは静的整形違反か型エラーによるものであり、
UB 起因ではない。
-/
theorem error_implies_static_violation
    (Γ : TyEnv) (stbl : StructTable) (retTy : CppType)
    (s : State) (st : CppStmt) (n : Nat)
    (h : WF_Typed_Safe Γ stbl retTy s st)
    (e : EvalError) (s' : State)
    (herr : evalStmt n s st = .error e s') :
    e.category.isMathematical ∨ e = .unsupported "call" := by
  sorry -- Phase 5 で証明

end ErrorClassification

-- ============================================================
-- §8. 具体的計算例（サニティチェック）
-- ============================================================

section Examples

-- 例 1: リテラル評価
#eval evalExpr 10 State.empty (.lit (.int 42))
-- 期待値: EvalResult.ok (ExprResult.rval (RValue.int 42)) State.empty

-- 例 2: 1 + 2
#eval evalExpr 10 State.empty (.binop .add (.lit (.int 1)) (.lit (.int 2)))
-- 期待値: EvalResult.ok (ExprResult.rval (RValue.int 3)) State.empty

-- 例 3: skip 文
#eval evalStmt 10 State.empty .skip
-- 期待値: EvalResult.ok Control.normal State.empty

-- 例 4: return 42
#eval evalStmt 10 State.empty (.return_ (some (.lit (.int 42))))
-- 期待値: EvalResult.ok (Control.return_ (RValue.int 42)) State.empty

-- 例 5: fuel = 0 → timeout
#eval evalStmt 0 State.empty .skip
-- 期待値: EvalResult.timeout State.empty

-- 例 6: if (true) return 1 else return 2
#eval evalStmt 10 State.empty
    (.ite (.lit (.bool true))
          (.return_ (some (.lit (.int 1))))
          (.return_ (some (.lit (.int 2)))))
-- 期待値: EvalResult.ok (Control.return_ (RValue.int 1)) State.empty

-- 例 7: 変数宣言と読み取り
-- { int x = 10; return x; }
def exampleBlockReturn : CppStmt :=
  .block [
    .decl { type := CInt, name := "x", init := .direct (.lit (.int 10)) },
    .return_ (some (.var "x"))
  ]

#eval evalStmt 10 State.empty exampleBlockReturn
-- 期待値: EvalResult.ok (Control.return_ (RValue.int 10)) ...

-- 例 8: while ループ（カウントアップ）
-- { int i = 0; while (i < 3) { i = i + 1; } return i; }
def exampleWhileLoop : CppStmt :=
  .block [
    .decl { type := CInt, name := "i", init := .direct (.lit (.int 0)) },
    .while_
      (.binop .lt (.var "i") (.lit (.int 3)))
      (.expr (.assign .assign (.var "i")
                (.binop .add (.var "i") (.lit (.int 1))))),
    .return_ (some (.var "i"))
  ]

#eval evalStmt 50 State.empty exampleWhileLoop
-- 期待値: EvalResult.ok (Control.return_ (RValue.int 3)) ...

-- 例 9: fuel 切れ（無限ループは timeout）
def exampleInfiniteLoop : CppStmt :=
  .while_ (.lit (.bool true)) .skip

#eval evalStmt 5 State.empty exampleInfiniteLoop
-- 期待値: EvalResult.timeout ...

-- 例 10: break で while を抜ける
-- while (true) { break; }
def exampleBreak : CppStmt :=
  .while_ (.lit (.bool true)) .break_

#eval evalStmt 10 State.empty exampleBreak
-- 期待値: EvalResult.ok Control.normal ...

-- 例 11: 0 除算 → typeMismatch（stuck = semantics に規則なし）
#eval evalExpr 10 State.empty (.binop .div (.lit (.int 1)) (.lit (.int 0)))
-- 期待値: EvalResult.error EvalError.typeMismatch ...

-- 例 12: fuel 単調性のチェック
-- "fuel 5 で成功したなら fuel 100 でも成功する" を #eval で確認
#eval (evalExpr 5 State.empty (.lit (.int 1)),
       evalExpr 100 State.empty (.lit (.int 1)))
-- 期待値: 両方とも .ok (.rval (.int 1))

end Examples

end Cpp
