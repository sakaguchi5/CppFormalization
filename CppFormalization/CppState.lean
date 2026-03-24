import CppFormalization.CppSyntax

namespace Cpp

/-
Phase 1.5 / NoUB 仮定版のための状態モデル。

設計原理:
1. rvalue と lvalue を分離する。
2. Value と aggregate object を分離する。
3. 環境は「global root + local frame stack」として表す。
4. store の各 cell は alive / initialized を持つ。
5. evaluator の失敗は timeout / runtime error を分離する。

このファイルは eval 本体ではなく、その後の意味論・健全性・
エラー分類が崩れないための土台を与える。
-/

-- ============================================================
-- §1. 連想リストの最小基盤
-- ============================================================

namespace Assoc

abbrev Map (α β : Type) := List (α × β)

def lookup [BEq α] : Map α β → α → Option β
  | [], _ => none
  | (k, v) :: xs, x =>
      if k == x then some v else lookup xs x

def upsert [BEq α] : Map α β → α → β → Map α β
  | [], x, v => [(x, v)]
  | (k, w) :: xs, x, v =>
      if k == x then (x, v) :: xs
      else (k, w) :: upsert xs x v

def modify? [BEq α] : Map α β → α → (β → β) → Option (Map α β)
  | [], _, _ => none
  | (k, v) :: xs, x, f =>
      if k == x then
        some ((k, f v) :: xs)
      else
        match modify? xs x f with
        | none => none
        | some xs' => some ((k, v) :: xs')

def erase [BEq α] : Map α β → α → Map α β
  | [], _ => []
  | (k, v) :: xs, x =>
      if k == x then xs else (k, v) :: erase xs x

def keys : Map α β → List α
  | [] => []
  | (k, _) :: xs => k :: keys xs

def NoDupKeys [DecidableEq α] (m : Map α β) : Prop :=
  (keys m).Nodup

end Assoc

namespace LocalList

def All {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ All P xs

end LocalList

-- ============================================================
-- §2. エラーの骨格
-- ============================================================

abbrev Loc := Nat

def nullLoc : Loc := 0

inductive EvalError : Type where
  | unboundVar        : Ident → EvalError
  | invalidLoc        : Loc → EvalError
  | uninitializedRead : Loc → EvalError
  | notAssignable     : EvalError
  | nullDeref         : EvalError
  | outOfBounds       : EvalError
  | useAfterFree      : Loc → EvalError
  | invalidCast       : EvalError
  | aggregateRValue   : EvalError
  | missingField      : Ident → EvalError
  | arityMismatch     : Nat → Nat → EvalError
  | typeMismatch      : EvalError
  | scopeUnderflow    : EvalError
  | unsupported       : String → EvalError
  deriving Repr, BEq

-- ============================================================
-- §3. 値とオブジェクト
-- ============================================================

inductive RValue : Type where
  | void  : RValue
  | int   : Int → RValue
  | uint  : Nat → RValue
  | float : Float → RValue
  | bool  : Bool → RValue
  | ptr   : Loc → RValue
  deriving Repr, BEq

inductive Object : Type where
  | scalar  : RValue → Object
  | array   : CppType → List Loc → Object
  | struct_ : Ident → List (Ident × Loc) → Object
  deriving Repr, BEq

namespace Object

def fieldLoc? : Object → Ident → Option Loc
  | .scalar _, _ => none
  | .array _ _, _ => none
  | .struct_ _ fields, name => Assoc.lookup fields name

def indexLoc? : Object → Nat → Option Loc
  | .scalar _, _ => none
  | .struct_ _ _, _ => none
  | .array _ locs, i => locs[i]?

end Object

inductive StorageClass : Type where
  | global
  | stack
  | heap
  deriving Repr, DecidableEq, BEq

structure Cell : Type where
  ty          : CppType
  object      : Object
  storage     : StorageClass
  initialized : Bool
  alive       : Bool
  deriving Repr, BEq

namespace Cell

def isReadable (c : Cell) : Bool :=
  c.alive && c.initialized

def toScalar? (c : Cell) : Option RValue :=
  if !c.alive then
    none
  else if !c.initialized then
    none
  else
    match c.object with
    | .scalar v => some v
    | .array _ _ => none
    | .struct_ _ _ => none

def kill (c : Cell) : Cell :=
  { c with alive := false }

def overwriteScalar (c : Cell) (v : RValue) : Cell :=
  { c with object := .scalar v, initialized := true }

def overwriteObject (c : Cell) (obj : Object) : Cell :=
  { c with object := obj, initialized := true }

end Cell

-- ============================================================
-- §4. フレームと環境
-- ============================================================

structure Frame : Type where
  bindings : List (Ident × Loc)
  owned    : List Loc
  deriving Repr, BEq

namespace Frame

def empty : Frame :=
  { bindings := [], owned := [] }

def lookup (fr : Frame) (x : Ident) : Option Loc :=
  Assoc.lookup fr.bindings x

def bind (fr : Frame) (x : Ident) (l : Loc) : Frame :=
  { fr with bindings := Assoc.upsert fr.bindings x l }

def own (fr : Frame) (l : Loc) : Frame :=
  if fr.owned.contains l then fr else { fr with owned := l :: fr.owned }

def WF (fr : Frame) : Prop :=
  Assoc.NoDupKeys fr.bindings

end Frame

/--
環境は「必ず存在する global root」と「0 個以上の local frame stack」からなる。
local stack の先頭が最内側スコープ。
-/
structure Env : Type where
  global : Frame
  locals : List Frame
  deriving Repr, BEq

namespace Env

def empty : Env :=
  { global := Frame.empty, locals := [] }

private def lookupLocals : List Frame → Ident → Option Loc
  | [], _ => none
  | fr :: rest, x =>
      match fr.lookup x with
      | some l => some l
      | none => lookupLocals rest x

def lookup (env : Env) (x : Ident) : Option Loc :=
  match lookupLocals env.locals x with
  | some l => some l
  | none => env.global.lookup x

def enterScope (env : Env) : Env :=
  { env with locals := Frame.empty :: env.locals }

/--
最内側 local scope を 1 つ外す。
返り値の Frame は、その scope が所有していた stack loc を回収するために使う。
-/
def exitScope : Env → Option (Frame × Env)
  | ⟨_g, []⟩ => none
  | ⟨g, fr :: rest⟩ => some (fr, ⟨g, rest⟩)

def bindGlobal (env : Env) (x : Ident) (l : Loc) : Env :=
  { env with global := env.global.bind x l }

def bindCurrentLocal? : Env → Ident → Loc → Option Env
  | ⟨_g, []⟩, _, _ => none
  | ⟨g, fr :: rest⟩, x, l =>
      some ⟨g, (fr.bind x l) :: rest⟩

def ownCurrentLocal? : Env → Loc → Option Env
  | ⟨_g, []⟩, _ => none
  | ⟨g, fr :: rest⟩, l =>
      some ⟨g, (fr.own l) :: rest⟩

def WF (env : Env) : Prop :=
  Frame.WF env.global ∧ LocalList.All Frame.WF env.locals

end Env

-- ============================================================
-- §5. store と各種テーブル
-- ============================================================

abbrev Store := List (Loc × Cell)
abbrev FuncTable := List (Ident × FuncDef)
abbrev StructTable := List (Ident × List MemberDecl)

namespace Store

def read (st : Store) (l : Loc) : Option Cell :=
  Assoc.lookup st l

def write (st : Store) (l : Loc) (c : Cell) : Store :=
  Assoc.upsert st l c

def modify? (st : Store) (l : Loc) (f : Cell → Cell) : Option Store :=
  Assoc.modify? st l f

def killMany (st : Store) : List Loc → Store
  | [] => st
  | l :: ls =>
      let st' :=
        match modify? st l Cell.kill with
        | some st' => st'
        | none => st
      killMany st' ls

def WF (st : Store) : Prop :=
  Assoc.NoDupKeys st

end Store

namespace FuncTable

def lookup (ft : FuncTable) (f : Ident) : Option FuncDef :=
  Assoc.lookup ft f

def WF (ft : FuncTable) : Prop :=
  Assoc.NoDupKeys ft

end FuncTable

namespace StructTable

def lookup (st : StructTable) (name : Ident) : Option (List MemberDecl) :=
  Assoc.lookup st name

def WF (st : StructTable) : Prop :=
  Assoc.NoDupKeys st

end StructTable

-- ============================================================
-- §6. 実行状態
-- ============================================================

structure State : Type where
  env     : Env
  store   : Store
  funcs   : FuncTable
  structs : StructTable
  nextLoc : Loc
  deriving Repr

namespace State

def empty : State :=
  {
    env := Env.empty,
    store := [],
    funcs := [],
    structs := [],
    nextLoc := 1
  }

def WF (s : State) : Prop :=
  Env.WF s.env ∧
  Store.WF s.store ∧
  FuncTable.WF s.funcs ∧
  StructTable.WF s.structs ∧
  s.nextLoc ≠ nullLoc

def locOf (s : State) (x : Ident) : Option Loc :=
  Env.lookup s.env x

def readCell (s : State) (l : Loc) : Option Cell :=
  Store.read s.store l

def writeCell (s : State) (l : Loc) (c : Cell) : State :=
  { s with store := Store.write s.store l c }

def modifyCell? (s : State) (l : Loc) (f : Cell → Cell) : Option State :=
  match Store.modify? s.store l f with
  | none => none
  | some st' => some { s with store := st' }

def allocCell (s : State) (c : Cell) : Loc × State :=
  let l := s.nextLoc
  let s' :=
    { s with
      store := Store.write s.store l c,
      nextLoc := s.nextLoc + 1 }
  (l, s')

def bindGlobal (s : State) (x : Ident) (l : Loc) : State :=
  { s with env := Env.bindGlobal s.env x l }

def bindCurrentLocal? (s : State) (x : Ident) (l : Loc) : Option State :=
  match Env.bindCurrentLocal? s.env x l with
  | none => none
  | some env' => some { s with env := env' }

def ownCurrentLocal? (s : State) (l : Loc) : Option State :=
  match Env.ownCurrentLocal? s.env l with
  | none => none
  | some env' => some { s with env := env' }

def enterScope (s : State) : State :=
  { s with env := Env.enterScope s.env }

end State

-- ============================================================
-- §7. 評価結果と制御結果
-- ============================================================

inductive EvalResult (α : Type) : Type where
  | ok      : α → State → EvalResult α
  | error   : EvalError → State → EvalResult α
  | timeout : State → EvalResult α
  deriving Repr

namespace EvalResult

variable {α β : Type}

def state : EvalResult α → State
  | .ok _ s => s
  | .error _ s => s
  | .timeout s => s

def map (f : α → β) : EvalResult α → EvalResult β
  | .ok a s => .ok (f a) s
  | .error e s => .error e s
  | .timeout s => .timeout s

def bind (r : EvalResult α) (f : α → State → EvalResult β) : EvalResult β :=
  match r with
  | .ok a s => f a s
  | .error e s => .error e s
  | .timeout s => .timeout s

def pure (a : α) (s : State) : EvalResult α :=
  .ok a s

end EvalResult

inductive ExprResult : Type where
  | rval : RValue → ExprResult
  | lval : Loc → ExprResult
  deriving Repr, BEq

namespace ExprResult

def toLoc (r : ExprResult) (s : State) : EvalResult Loc :=
  match r with
  | .lval l => .ok l s
  | .rval _ => .error .notAssignable s

def toRValue (r : ExprResult) (s : State) : EvalResult RValue :=
  match r with
  | .rval v => .ok v s
  | .lval l =>
      match s.readCell l with
      | none => .error (.invalidLoc l) s
      | some c =>
          if !c.alive then
            .error (.useAfterFree l) s
          else if !c.initialized then
            .error (.uninitializedRead l) s
          else
            match c.object with
            | .scalar v => .ok v s
            | .array _ _ => .error .aggregateRValue s
            | .struct_ _ _ => .error .aggregateRValue s

end ExprResult

inductive Control : Type where
  | normal    : Control
  | break_    : Control
  | continue_ : Control
  | return_   : RValue → Control
  deriving Repr, BEq

abbrev StmtResult := EvalResult Control

-- ============================================================
-- §8. 状態操作の補助関数
-- ============================================================

namespace State

def varLValue (s : State) (x : Ident) : EvalResult ExprResult :=
  match s.locOf x with
  | none => .error (.unboundVar x) s
  | some l => .ok (.lval l) s

def readObject (s : State) (l : Loc) : EvalResult Object :=
  match s.readCell l with
  | none => .error (.invalidLoc l) s
  | some c =>
      if !c.alive then
        .error (.useAfterFree l) s
      else if !c.initialized then
        .error (.uninitializedRead l) s
      else
        .ok c.object s

def writeScalar (s : State) (l : Loc) (v : RValue) : EvalResult PUnit :=
  match s.readCell l with
  | none => .error (.invalidLoc l) s
  | some c =>
      if !c.alive then
        .error (.useAfterFree l) s
      else
        match s.modifyCell? l (fun c => c.overwriteScalar v) with
        | none => .error (.invalidLoc l) s
        | some s' => .ok PUnit.unit s'

def writeObject (s : State) (l : Loc) (obj : Object) : EvalResult PUnit :=
  match s.readCell l with
  | none => .error (.invalidLoc l) s
  | some c =>
      if !c.alive then
        .error (.useAfterFree l) s
      else
        match s.modifyCell? l (fun c => c.overwriteObject obj) with
        | none => .error (.invalidLoc l) s
        | some s' => .ok PUnit.unit s'

/-- global 変数宣言。global root に束縛する。 -/
def declareGlobalObject
    (s : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true)
    : EvalResult Loc :=
  let cell : Cell :=
    { ty := ty, object := obj, storage := .global, initialized := initialized, alive := true }
  let (l, s1) := s.allocCell cell
  let s2 := s1.bindGlobal x l
  .ok l s2

/-- stack 変数宣言。現在の local scope が存在しないと失敗する。 -/
def declareStackObject
    (s : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true)
    : EvalResult Loc :=
  let cell : Cell :=
    { ty := ty, object := obj, storage := .stack, initialized := initialized, alive := true }
  let (l, s1) := s.allocCell cell
  match s1.bindCurrentLocal? x l with
  | none => .error .scopeUnderflow s
  | some s2 =>
      match s2.ownCurrentLocal? l with
      | none => .error .scopeUnderflow s
      | some s3 => .ok l s3

/-- heap object を確保し、ポインタ rvalue を返す。 -/
def allocHeapObject
    (s : State) (ty : CppType) (obj : Object) (initialized : Bool := true)
    : EvalResult RValue :=
  let cell : Cell :=
    { ty := ty, object := obj, storage := .heap, initialized := initialized, alive := true }
  let (l, s') := s.allocCell cell
  .ok (.ptr l) s'

/-- local scope を 1 つ閉じ、その frame 所有の stack loc を dead にする。 -/
def exitScope (s : State) : EvalResult PUnit :=
  match Env.exitScope s.env with
  | none => .error .scopeUnderflow s
  | some (fr, env') =>
      let s' :=
        { s with
          env := env',
          store := Store.killMany s.store fr.owned }
      .ok PUnit.unit s'

end State

-- ============================================================
-- §9. eval シグネチャ
-- ============================================================

abbrev EvalExprSig := Nat → State → CppExpr → EvalResult ExprResult
abbrev EvalStmtSig := Nat → State → CppStmt → StmtResult

-- ============================================================
-- §10. 軽いサニティチェック
-- ============================================================

section Examples

  def exState0 : State := State.empty

  def exState1 : State := exState0.enterScope

  def exDecl : EvalResult Loc :=
    exState1.declareStackObject "x" CInt (.scalar (.int 42))

  def exReadBack : EvalResult RValue :=
    match exDecl with
    | .ok l s => ExprResult.toRValue (.lval l) s
    | .error e s => .error e s
    | .timeout s => .timeout s

  def exCloseScope : StmtResult :=
    match exDecl with
    | .ok _ s => EvalResult.map (fun _ => Control.normal) (s.exitScope)
    | .error e s => .error e s
    | .timeout s => .timeout s
/-
  #eval match exDecl with
    | .ok l s => (l, s.nextLoc)
    | .error _ _ => (0, 0)
    | .timeout _ => (0, 0)

  #eval exReadBack

  #eval exCloseScope
  -/
end Examples
/-
#eval
  match exCloseScope with
  | .ok _ s    => ExprResult.toRValue (.lval 1) s
  | .error e s => .error e s
  | .timeout s => .timeout s
-/

-- ============================================================
-- §10. Basic invariants
-- ============================================================

section BasicInvariants

  theorem toLoc_lval (l : Loc) (s : State) :
      ExprResult.toLoc (.lval l) s = .ok l s := by
    rfl

  theorem toLoc_rval_notAssignable (v : RValue) (s : State) :
      ExprResult.toLoc (.rval v) s = .error .notAssignable s := by
    rfl

  theorem toRValue_rval (v : RValue) (s : State) :
      ExprResult.toRValue (.rval v) s = .ok v s := by
    rfl

  theorem toRValue_dead_cell_gives_useAfterFree
      (s : State) (l : Loc) (c : Cell)
      (hread : s.readCell l = some c)
      (halive : c.alive = false) :
      ExprResult.toRValue (.lval l) s = .error (.useAfterFree l) s := by
    simp [ExprResult.toRValue, hread, halive]

  theorem toRValue_uninitialized_cell_gives_uninitializedRead
      (s : State) (l : Loc) (c : Cell)
      (hread : s.readCell l = some c)
      (halive : c.alive = true)
      (hinit : c.initialized = false) :
      ExprResult.toRValue (.lval l) s = .error (.uninitializedRead l) s := by
    simp [ExprResult.toRValue, hread, halive, hinit]
/- 定義済み
  def exState0 : State := State.empty

  def exState1 : State := exState0.enterScope
-/
  def exCellAlive : Cell :=
    { ty := CInt
    , object := .scalar (.int 42)
    , storage := .stack
    , initialized := true
    , alive := true
    }

  def exCellDead : Cell :=
    { exCellAlive with alive := false }

  def exStateAfterDecl : State :=
    { env :=
        { global := { bindings := [], owned := [] }
        , locals := [{ bindings := [("x", 1)], owned := [1] }]
        }
    , store := [(1, exCellAlive)]
    , funcs := []
    , structs := []
    , nextLoc := 2
    }

  def exStateAfterClose : State :=
    { env :=
        { global := { bindings := [], owned := [] }
        , locals := []
        }
    , store := [(1, exCellDead)]
    , funcs := []
    , structs := []
    , nextLoc := 2
    }
/-　定義済み
  def exDecl : EvalResult Loc :=
    exState1.declareStackObject "x" CInt (.scalar (.int 42))

  def exReadBack : EvalResult RValue :=
    match exDecl with
    | .ok l s => ExprResult.toRValue (.lval l) s
    | .error e s => .error e s
    | .timeout s => .timeout s

  def exCloseScope : StmtResult :=
    match exDecl with
    | .ok _ s => EvalResult.map (fun _ => Control.normal) (s.exitScope)
    | .error e s => .error e s
    | .timeout s => .timeout s
-/
  def exReadAfterClose : EvalResult RValue :=
    match exCloseScope with
    | .ok _ s => ExprResult.toRValue (.lval 1) s
    | .error e s => .error e s
    | .timeout s => .timeout s

  theorem exDecl_eq :
      exDecl = .ok 1 exStateAfterDecl := by
    rfl

  theorem exReadBack_eq :
      exReadBack = .ok (.int 42) exStateAfterDecl := by
    rfl

  theorem exCloseScope_eq :
      exCloseScope = .ok Control.normal exStateAfterClose := by
    rfl

  theorem exReadAfterClose_eq :
      exReadAfterClose = .error (.useAfterFree 1) exStateAfterClose := by
    rfl

  theorem exClosedCellIsDead :
      exStateAfterClose.readCell 1 = some exCellDead := by
    rfl

  theorem exDeadReadIsUseAfterFree :
      ExprResult.toRValue (.lval 1) exStateAfterClose
        = .error (.useAfterFree 1) exStateAfterClose := by
    rfl

end BasicInvariants


-- ============================================================
-- §11. Scope / declaration contracts
-- ============================================================

section ScopeDeclarationContracts

  theorem enterScope_preserves_store
      (s : State) :
      (s.enterScope).store = s.store := by
    rfl

  theorem enterScope_preserves_nextLoc
      (s : State) :
      (s.enterScope).nextLoc = s.nextLoc := by
    rfl

  theorem enterScope_preserves_funcs
      (s : State) :
      (s.enterScope).funcs = s.funcs := by
    rfl

  theorem enterScope_preserves_structs
      (s : State) :
      (s.enterScope).structs = s.structs := by
    rfl

  private theorem exitScope_nil_not_ok
    (store : Store) (funcs : FuncTable) (structs : StructTable)
    (nextLoc : Loc) (global : Frame) (s' : State) :
    ({ env := { global := global, locals := [] }
     , store := store
     , funcs := funcs
     , structs := structs
     , nextLoc := nextLoc
     } : State).exitScope
    ≠
    EvalResult.ok () s' := by
  intro h
  have h' :
      EvalResult.error EvalError.scopeUnderflow
        { env := { global := global, locals := [] }
        , store := store
        , funcs := funcs
        , structs := structs
        , nextLoc := nextLoc
        }
      =
      EvalResult.ok () s' := by
    simp [State.exitScope, Env.exitScope] at h
  cases h'

  theorem exitScope_success_preserves_global
      (s s' : State)
      (h : s.exitScope = .ok () s') :
      s'.env.global = s.env.global := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact exitScope_nil_not_ok store funcs structs nextLoc global s' h
            | cons top rest =>
                simp [State.exitScope] at h
                cases h
                rfl

  theorem exitScope_success_preserves_funcs
      (s s' : State)
      (h : s.exitScope = .ok () s') :
      s'.funcs = s.funcs := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact exitScope_nil_not_ok store funcs structs nextLoc global s' h
            | cons top rest =>
                simp [State.exitScope] at h
                cases h
                rfl

  theorem exitScope_success_preserves_structs
      (s s' : State)
      (h : s.exitScope = .ok () s') :
      s'.structs = s.structs := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact exitScope_nil_not_ok store funcs structs nextLoc global s' h
            | cons top rest =>
                simp [State.exitScope] at h
                cases h
                rfl

  theorem exitScope_success_preserves_nextLoc
      (s s' : State)
      (h : s.exitScope = .ok () s') :
      s'.nextLoc = s.nextLoc := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact exitScope_nil_not_ok store funcs structs nextLoc global s' h
            | cons top rest =>
                simp [State.exitScope] at h
                cases h
                rfl

private theorem bindCurrentLocal?_nil_eq_none
    (global : Frame) (store : Store) (funcs : FuncTable) (structs : StructTable)
    (nextLoc : Loc) (x : Ident) (l : Loc) :
    ({ env := { global := global, locals := [] }
     , store := store
     , funcs := funcs
     , structs := structs
     , nextLoc := nextLoc
     } : State).bindCurrentLocal? x l = none := by
  simp [State.bindCurrentLocal?, Env.bindCurrentLocal?]

private theorem ownCurrentLocal?_nil_eq_none
    (global : Frame) (store : Store) (funcs : FuncTable) (structs : StructTable)
    (nextLoc : Loc) (l : Loc) :
    ({ env := { global := global, locals := [] }
     , store := store
     , funcs := funcs
     , structs := structs
     , nextLoc := nextLoc
     } : State).ownCurrentLocal? l = none := by
  simp [State.ownCurrentLocal?, Env.ownCurrentLocal?]

private theorem allocCell_preserves_env
    (s : State) (cell : Cell) :
    (s.allocCell cell).snd.env = s.env := by
  simp [State.allocCell]

private theorem declareStackObject_nil_not_ok
    (store : Store) (funcs : FuncTable) (structs : StructTable)
    (nextLoc : Loc) (global : Frame)
    (x : Ident) (ty : CppType) (obj : Object)
    (l : Loc) (s' : State) :
    ({ env := { global := global, locals := [] }
     , store := store
     , funcs := funcs
     , structs := structs
     , nextLoc := nextLoc
     } : State).declareStackObject x ty obj
    ≠ EvalResult.ok l s' := by
  intro h
  unfold State.declareStackObject at h
  let s0 : State :=
    { env := { global := global, locals := [] }
    , store := store
    , funcs := funcs
    , structs := structs
    , nextLoc := nextLoc
    }
  let cell : Cell :=
    { ty := ty
    , object := obj
    , storage := StorageClass.stack
    , initialized := true
    , alive := true
    }
  cases halloc : s0.allocCell cell with
  | mk l0 s1 =>
      have hs1env' : (s0.allocCell cell).snd.env = s0.env := by
        simpa [s0, cell] using allocCell_preserves_env s0 cell
      have hs1env : s1.env = s0.env := by
        simpa [halloc] using hs1env'
      have hbind : s1.bindCurrentLocal? x l0 = none := by
        rw [State.bindCurrentLocal?]
        rw [hs1env]
        simp [s0, Env.bindCurrentLocal?]

      have h' :
          (match s0.allocCell cell with
           | (l, s1) =>
               match s1.bindCurrentLocal? x l with
               | none =>
                   EvalResult.error EvalError.scopeUnderflow s0
               | some s2 =>
                   match s2.ownCurrentLocal? l with
                   | none => EvalResult.error EvalError.scopeUnderflow s0
                   | some s3 => EvalResult.ok l s3) =
          EvalResult.ok l s' := by
        simpa [s0, cell] using h

      rw [halloc] at h'
      simp [hbind] at h'

  private theorem allocCell_fresh
    (s : State) (cell : Cell) :
    (s.allocCell cell).fst = s.nextLoc := by
  simp [State.allocCell]

  theorem declareStackObject_success_nextLoc
      (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (l : Loc)
      (h : s.declareStackObject x ty obj = .ok l s') :
      s'.nextLoc = s.nextLoc + 1 := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact declareStackObject_nil_not_ok
                  store funcs structs nextLoc global x ty obj l s' h
            | cons top rest =>
                simp [State.declareStackObject] at h
                cases h
                rfl

  theorem declareStackObject_success_fresh
      (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (l : Loc)
      (h : s.declareStackObject x ty obj = .ok l s') :
      l = s.nextLoc := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact declareStackObject_nil_not_ok
                  store funcs structs nextLoc global x ty obj l s' h
            | cons top rest =>
                simp [State.declareStackObject] at h
                rcases h with ⟨rfl⟩
                rfl

  theorem declareStackObject_success_preserves_global
      (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (l : Loc)
      (h : s.declareStackObject x ty obj = .ok l s') :
      s'.env.global = s.env.global := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact declareStackObject_nil_not_ok
                  store funcs structs nextLoc global x ty obj l s' h
            | cons top rest =>
                simp [State.declareStackObject] at h
                rcases h with ⟨rfl⟩
                rfl

  theorem declareStackObject_success_preserves_funcs
      (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (l : Loc)
      (h : s.declareStackObject x ty obj = .ok l s') :
      s'.funcs = s.funcs := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact declareStackObject_nil_not_ok
                  store funcs structs nextLoc global x ty obj l s' h
            | cons top rest =>
                simp [State.declareStackObject] at h
                rcases h with ⟨rfl⟩
                rfl

  theorem declareStackObject_success_preserves_structs
      (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (l : Loc)
      (h : s.declareStackObject x ty obj = .ok l s') :
      s'.structs = s.structs := by
    cases s with
    | mk env store funcs structs nextLoc =>
        cases env with
        | mk global locals =>
            cases locals with
            | nil =>
                exfalso
                exact declareStackObject_nil_not_ok
                  store funcs structs nextLoc global x ty obj l s' h
            | cons top rest =>
                simp [State.declareStackObject] at h
                rcases h with ⟨rfl⟩
                rfl

end ScopeDeclarationContracts



end Cpp
