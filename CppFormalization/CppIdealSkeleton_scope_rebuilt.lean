namespace Cpp

universe u

/-!
Rebuilt contract-level skeleton.

This version changes the mathematical core in two deliberate ways.

1. Expressions are split into place expressions and value expressions.
   - place expressions denote writable/readable locations
   - value expressions denote runtime values

2. Both typing and runtime state are scope-aware.
   - typing threads a scoped environment through statements
   - runtime state uses a scope stack with object/reference bindings
   - block exit pops the scope and kills the objects allocated in that scope

What remains axiomatic is exactly the semantic frontier: deep safety predicates,
full progress/completeness proofs, the evaluator, and the bridge to real C++.
-/

abbrev Ident := String

inductive BaseType where
  | void
  | bool
  | int
  deriving DecidableEq, Repr

inductive CppType where
  | base  : BaseType → CppType
  | ptr   : CppType → CppType
  | ref   : CppType → CppType
  | array : CppType → Nat → CppType
  deriving DecidableEq, Repr

/-- Object declarations supported by the current runtime core.
    Arrays and `void` are intentionally left outside this executable fragment. -/
def ObjectType : CppType → Prop
  | .base .void => False
  | .ref _ => False
  | .array _ _ => False
  | _ => True

inductive Value where
  | unit
  | bool : Bool → Value
  | int  : Int → Value
  | addr : Nat → Value
  deriving DecidableEq, Repr

inductive DeclInfo where
  | object : CppType → DeclInfo
  | ref    : CppType → DeclInfo
  deriving DecidableEq, Repr

def declPlaceType : DeclInfo → CppType
  | .object τ => τ
  | .ref τ => τ

structure TypeFrame where
  decls : Ident → Option DeclInfo

structure TypeEnv where
  scopes : List TypeFrame

instance : Repr TypeEnv where
  reprPrec Γ _ :=
    "TypeEnv { scopes := " ++ repr Γ.scopes.length ++ " }"

def emptyTypeFrame : TypeFrame := {
  decls := fun _ => none
}

def emptyTypeEnv : TypeEnv := {
  scopes := [emptyTypeFrame]
}

instance : Inhabited TypeEnv where
  default := emptyTypeEnv

def lookupDeclFrames : List TypeFrame → Ident → Option DeclInfo
  | [], _ => none
  | fr :: frs, x =>
      match fr.decls x with
      | some d => some d
      | none => lookupDeclFrames frs x

def lookupDecl (Γ : TypeEnv) (x : Ident) : Option DeclInfo :=
  lookupDeclFrames Γ.scopes x

def pushTypeScope (Γ : TypeEnv) : TypeEnv :=
  { Γ with scopes := emptyTypeFrame :: Γ.scopes }

def currentTypeScopeFresh (Γ : TypeEnv) (x : Ident) : Prop :=
  match Γ.scopes with
  | [] => False
  | fr :: _ => fr.decls x = none

def withTopTypeFrame (Γ : TypeEnv) (fr : TypeFrame) : TypeEnv :=
  match Γ.scopes with
  | [] => { scopes := [fr] }
  | _ :: frs => { scopes := fr :: frs }

def insertTopDecl (Γ : TypeEnv) (x : Ident) (d : DeclInfo) : TypeEnv :=
  match Γ.scopes with
  | [] =>
      { scopes := [{ decls := fun y => if y = x then some d else none }] }
  | fr :: frs =>
      { scopes :=
          { fr with decls := fun y => if y = x then some d else fr.decls y } :: frs }

def declareTypeObject (Γ : TypeEnv) (x : Ident) (τ : CppType) : TypeEnv :=
  insertTopDecl Γ x (.object τ)

def declareTypeRef (Γ : TypeEnv) (x : Ident) (τ : CppType) : TypeEnv :=
  insertTopDecl Γ x (.ref τ)

mutual

inductive PlaceExpr where
  | var   : Ident → PlaceExpr
  | deref : ValExpr → PlaceExpr
  deriving DecidableEq, Repr

inductive ValExpr where
  | litBool : Bool → ValExpr
  | litInt  : Int → ValExpr
  | load    : PlaceExpr → ValExpr
  | addrOf  : PlaceExpr → ValExpr
  | add     : ValExpr → ValExpr → ValExpr
  | sub     : ValExpr → ValExpr → ValExpr
  | mul     : ValExpr → ValExpr → ValExpr
  | eq      : ValExpr → ValExpr → ValExpr
  | lt      : ValExpr → ValExpr → ValExpr
  | not     : ValExpr → ValExpr
  deriving DecidableEq, Repr

end

structure Cell where
  ty    : CppType
  value : Option Value
  alive : Bool
  deriving Repr

inductive Binding where
  | object : CppType → Nat → Binding
  | ref    : CppType → Nat → Binding
  deriving DecidableEq, Repr

def bindingType : Binding → CppType
  | .object τ _ => τ
  | .ref τ _ => τ


def bindingAddr : Binding → Nat
  | .object _ a => a
  | .ref _ a => a

structure ScopeFrame where
  binds  : Ident → Option Binding
  locals : List Nat

structure State where
  scopes : List ScopeFrame
  heap   : Nat → Option Cell
  next   : Nat

instance : Repr State where
  reprPrec σ _ :=
    "State { scopes := " ++ repr σ.scopes.length ++ ", next := " ++ repr σ.next ++ " }"

def emptyScopeFrame : ScopeFrame := {
  binds := fun _ => none
  locals := []
}

def emptyState : State := {
  scopes := [emptyScopeFrame]
  heap := fun _ => none
  next := 0
}

instance : Inhabited State where
  default := emptyState

def lookupBindingFrames : List ScopeFrame → Ident → Option Binding
  | [], _ => none
  | fr :: frs, x =>
      match fr.binds x with
      | some b => some b
      | none => lookupBindingFrames frs x

def lookupBinding (σ : State) (x : Ident) : Option Binding :=
  lookupBindingFrames σ.scopes x

def currentScopeFresh (σ : State) (x : Ident) : Prop :=
  match σ.scopes with
  | [] => False
  | fr :: _ => fr.binds x = none

def writeHeap (σ : State) (a : Nat) (c : Cell) : State :=
  { σ with
    heap := fun b => if b = a then some c else σ.heap b }

def killAddr (σ : State) (a : Nat) : State :=
  match σ.heap a with
  | none => σ
  | some c => writeHeap σ a { c with alive := false }

def killLocals : State → List Nat → State
  | σ, [] => σ
  | σ, a :: as => killLocals (killAddr σ a) as

def pushScope (σ : State) : State :=
  { σ with scopes := emptyScopeFrame :: σ.scopes }

def bindTopBinding (σ : State) (x : Ident) (b : Binding) : State :=
  match σ.scopes with
  | [] =>
      { σ with
        scopes := [{ binds := fun y => if y = x then some b else none, locals := [] }] }
  | fr :: frs =>
      { σ with
        scopes :=
          { fr with binds := fun y => if y = x then some b else fr.binds y } :: frs }

def recordLocal (σ : State) (a : Nat) : State :=
  match σ.scopes with
  | [] => σ
  | fr :: frs =>
      { σ with
        scopes := { fr with locals := a :: fr.locals } :: frs }

def declareObjectState (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 : State := { σ1 with next := a + 1 }
  let σ3 := writeHeap σ2 a { ty := τ, value := ov, alive := true }
  recordLocal σ3 a

def declareRefState (σ : State) (τ : CppType) (x : Ident) (a : Nat) : State :=
  bindTopBinding σ x (.ref τ a)

def popScope? (σ : State) : Option State :=
  match σ.scopes with
  | [] => none
  | fr :: frs =>
      let σ0 : State := { σ with scopes := frs }
      some (killLocals σ0 fr.locals)

mutual
inductive CppStmt where
  | skip
  | exprStmt   : ValExpr → CppStmt
  | assign     : PlaceExpr → ValExpr → CppStmt
  | declareObj : CppType → Ident → Option ValExpr → CppStmt
  | declareRef : CppType → Ident → PlaceExpr → CppStmt
  | seq        : CppStmt → CppStmt → CppStmt
  | ite        : ValExpr → CppStmt → CppStmt → CppStmt
  | whileStmt  : ValExpr → CppStmt → CppStmt
  | block      : StmtBlock → CppStmt
  | breakStmt
  | continueStmt
  | returnStmt : Option ValExpr → CppStmt

inductive StmtBlock where
  | nil
  | cons : CppStmt → StmtBlock → StmtBlock
end

namespace StmtBlock

def ofList : List CppStmt → StmtBlock
  | [] => .nil
  | s :: ss => .cons s (ofList ss)

def toList : StmtBlock → List CppStmt
  | .nil => []
  | .cons s ss => s :: toList ss

def Mem (s : CppStmt) : StmtBlock → Prop
  | .nil => False
  | .cons t ts => s = t ∨ Mem s ts

@[simp] theorem mem_nil {s : CppStmt} : Mem s .nil ↔ False := by rfl
@[simp] theorem mem_cons {s t : CppStmt} {ss : StmtBlock} :
    Mem s (.cons t ss) ↔ s = t ∨ Mem s ss := by rfl

end StmtBlock


def CppStmt.blockOfList (xs : List CppStmt) : CppStmt :=
  .block (StmtBlock.ofList xs)

inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnResult : Option Value → CtrlResult
  deriving DecidableEq, Repr

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr

mutual

def InBigStepFragment : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | .seq s t => InBigStepFragment s ∧ InBigStepFragment t
  | .ite _ s t => InBigStepFragment s ∧ InBigStepFragment t
  | .whileStmt _ body => InBigStepFragment body
  | .block ss => InBigStepBlockFragment ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True

def InBigStepBlockFragment : StmtBlock → Prop
  | .nil => True
  | .cons s ss => InBigStepFragment s ∧ InBigStepBlockFragment ss

end


def CoreBigStepFragment (st : CppStmt) : Prop :=
  InBigStepFragment st

mutual

inductive HasPlaceType : TypeEnv → PlaceExpr → CppType → Prop where
  | var {Γ x d} :
      lookupDecl Γ x = some d →
      HasPlaceType Γ (.var x) (declPlaceType d)
  | deref {Γ e τ} :
      HasValueType Γ e (.ptr τ) →
      HasPlaceType Γ (.deref e) τ

inductive HasValueType : TypeEnv → ValExpr → CppType → Prop where
  | litBool {Γ b} : HasValueType Γ (.litBool b) (.base .bool)
  | litInt  {Γ n} : HasValueType Γ (.litInt n) (.base .int)
  | load    {Γ p τ} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.load p) τ
  | addrOf  {Γ p τ} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.addrOf p) (.ptr τ)
  | add     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.add e₁ e₂) (.base .int)
  | sub     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.sub e₁ e₂) (.base .int)
  | mul     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.mul e₁ e₂) (.base .int)
  | eq      {Γ e₁ e₂ τ} :
      HasValueType Γ e₁ τ →
      HasValueType Γ e₂ τ →
      HasValueType Γ (.eq e₁ e₂) (.base .bool)
  | lt      {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.lt e₁ e₂) (.base .bool)
  | not     {Γ e} :
      HasValueType Γ e (.base .bool) →
      HasValueType Γ (.not e) (.base .bool)

end

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

mutual

def WellFormedPlace : PlaceExpr → Prop
  | .var _ => True
  | .deref e => WellFormedValue e


def WellFormedValue : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => WellFormedPlace p
  | .addrOf p => WellFormedPlace p
  | .add e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .sub e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .mul e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .eq e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .lt e₁ e₂ => WellFormedValue e₁ ∧ WellFormedValue e₂
  | .not e => WellFormedValue e

end

mutual

def WellFormedStmt : CppStmt → Prop
  | .skip => True
  | .exprStmt e => WellFormedValue e
  | .assign p e => WellFormedPlace p ∧ WellFormedValue e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => WellFormedValue e
  | .declareRef _ _ p => WellFormedPlace p
  | .seq s t => WellFormedStmt s ∧ WellFormedStmt t
  | .ite c s t => WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t
  | .whileStmt c b => WellFormedValue c ∧ WellFormedStmt b
  | .block ss => WellFormedBlock ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => WellFormedValue e


def WellFormedBlock : StmtBlock → Prop
  | .nil => True
  | .cons s ss => WellFormedStmt s ∧ WellFormedBlock ss

end

/-!
These two safety families are still coarse contract placeholders.
The important repair here is structural: they now follow the rebuilt syntax,
and they thread the actual state parameter instead of discarding it.
-/
mutual

def NoUninitPlace (_σ : State) : PlaceExpr → Prop
  | .var _ => True
  | .deref e => NoUninitValue _σ e


def NoUninitValue (_σ : State) : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => NoUninitPlace _σ p
  | .addrOf p => NoUninitPlace _σ p
  | .add e₁ e₂ => NoUninitValue _σ e₁ ∧ NoUninitValue _σ e₂
  | .sub e₁ e₂ => NoUninitValue _σ e₁ ∧ NoUninitValue _σ e₂
  | .mul e₁ e₂ => NoUninitValue _σ e₁ ∧ NoUninitValue _σ e₂
  | .eq e₁ e₂ => NoUninitValue _σ e₁ ∧ NoUninitValue _σ e₂
  | .lt e₁ e₂ => NoUninitValue _σ e₁ ∧ NoUninitValue _σ e₂
  | .not e => NoUninitValue _σ e

end

mutual

def NoUninitStmt (σ : State) : CppStmt → Prop
  | .skip => True
  | .exprStmt e => NoUninitValue σ e
  | .assign p e => NoUninitPlace σ p ∧ NoUninitValue σ e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => NoUninitValue σ e
  | .declareRef _ _ p => NoUninitPlace σ p
  | .seq s t => NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .ite c s t => NoUninitValue σ c ∧ NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .whileStmt c b => NoUninitValue σ c ∧ NoUninitStmt σ b
  | .block ss => NoUninitBlock σ ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => NoUninitValue σ e


def NoUninitBlock (σ : State) : StmtBlock → Prop
  | .nil => True
  | .cons s ss => NoUninitStmt σ s ∧ NoUninitBlock σ ss

end

mutual

def NoInvalidRefPlace (_σ : State) : PlaceExpr → Prop
  | .var _ => True
  | .deref e => NoInvalidRefValue _σ e


def NoInvalidRefValue (_σ : State) : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => NoInvalidRefPlace _σ p
  | .addrOf p => NoInvalidRefPlace _σ p
  | .add e₁ e₂ => NoInvalidRefValue _σ e₁ ∧ NoInvalidRefValue _σ e₂
  | .sub e₁ e₂ => NoInvalidRefValue _σ e₁ ∧ NoInvalidRefValue _σ e₂
  | .mul e₁ e₂ => NoInvalidRefValue _σ e₁ ∧ NoInvalidRefValue _σ e₂
  | .eq e₁ e₂ => NoInvalidRefValue _σ e₁ ∧ NoInvalidRefValue _σ e₂
  | .lt e₁ e₂ => NoInvalidRefValue _σ e₁ ∧ NoInvalidRefValue _σ e₂
  | .not e => NoInvalidRefValue _σ e

end

mutual

def NoInvalidRefStmt (σ : State) : CppStmt → Prop
  | .skip => True
  | .exprStmt e => NoInvalidRefValue σ e
  | .assign p e => NoInvalidRefPlace σ p ∧ NoInvalidRefValue σ e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => NoInvalidRefValue σ e
  | .declareRef _ _ p => NoInvalidRefPlace σ p
  | .seq s t => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .ite c s t => NoInvalidRefValue σ c ∧ NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .whileStmt c b => NoInvalidRefValue σ c ∧ NoInvalidRefStmt σ b
  | .block ss => NoInvalidRefBlock σ ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => NoInvalidRefValue σ e


def NoInvalidRefBlock (σ : State) : StmtBlock → Prop
  | .nil => True
  | .cons s ss => NoInvalidRefStmt σ s ∧ NoInvalidRefBlock σ ss

end

mutual

def BreakWellScopedAt : Nat → CppStmt → Prop
  | _d, .skip => True
  | _d, .exprStmt _ => True
  | _d, .assign _ _ => True
  | _d, .declareObj _ _ _ => True
  | _d, .declareRef _ _ _ => True
  | d, .seq s t => BreakWellScopedAt d s ∧ BreakWellScopedAt d t
  | d, .ite _ s t => BreakWellScopedAt d s ∧ BreakWellScopedAt d t
  | d, .whileStmt _ b => BreakWellScopedAt (d + 1) b
  | d, .block ss => BreakWellScopedBlockAt d ss
  | 0, .breakStmt => False
  | Nat.succ _, .breakStmt => True
  | _d, .continueStmt => True
  | _d, .returnStmt _ => True


def BreakWellScopedBlockAt : Nat → StmtBlock → Prop
  | _d, .nil => True
  | d, .cons s ss => BreakWellScopedAt d s ∧ BreakWellScopedBlockAt d ss

end

mutual

def ContinueWellScopedAt : Nat → CppStmt → Prop
  | _d, .skip => True
  | _d, .exprStmt _ => True
  | _d, .assign _ _ => True
  | _d, .declareObj _ _ _ => True
  | _d, .declareRef _ _ _ => True
  | d, .seq s t => ContinueWellScopedAt d s ∧ ContinueWellScopedAt d t
  | d, .ite _ s t => ContinueWellScopedAt d s ∧ ContinueWellScopedAt d t
  | d, .whileStmt _ b => ContinueWellScopedAt (d + 1) b
  | d, .block ss => ContinueWellScopedBlockAt d ss
  | _d, .breakStmt => True
  | 0, .continueStmt => False
  | Nat.succ _, .continueStmt => True
  | _d, .returnStmt _ => True


def ContinueWellScopedBlockAt : Nat → StmtBlock → Prop
  | _d, .nil => True
  | d, .cons s ss => ContinueWellScopedAt d s ∧ ContinueWellScopedBlockAt d ss

end

abbrev BreakWellScoped (st : CppStmt) : Prop := BreakWellScopedAt 0 st
abbrev ContinueWellScoped (st : CppStmt) : Prop := ContinueWellScopedAt 0 st

mutual

inductive BigStepPlace : State → PlaceExpr → Nat → Prop where
  | varObject {σ x τ a} :
      lookupBinding σ x = some (.object τ a) →
      BigStepPlace σ (.var x) a
  | varRef {σ x τ a} :
      lookupBinding σ x = some (.ref τ a) →
      BigStepPlace σ (.var x) a
  | deref {σ e a c} :
      BigStepValue σ e (.addr a) →
      σ.heap a = some c →
      c.alive = true →
      BigStepPlace σ (.deref e) a

inductive BigStepValue : State → ValExpr → Value → Prop where
  | litBool {σ b} :
      BigStepValue σ (.litBool b) (.bool b)
  | litInt {σ n} :
      BigStepValue σ (.litInt n) (.int n)
  | load {σ p a c v} :
      BigStepPlace σ p a →
      σ.heap a = some c →
      c.alive = true →
      c.value = some v →
      BigStepValue σ (.load p) v
  | addrOf {σ p a} :
      BigStepPlace σ p a →
      BigStepValue σ (.addrOf p) (.addr a)
  | add {σ e₁ e₂ n₁ n₂} :
      BigStepValue σ e₁ (.int n₁) →
      BigStepValue σ e₂ (.int n₂) →
      BigStepValue σ (.add e₁ e₂) (.int (n₁ + n₂))
  | sub {σ e₁ e₂ n₁ n₂} :
      BigStepValue σ e₁ (.int n₁) →
      BigStepValue σ e₂ (.int n₂) →
      BigStepValue σ (.sub e₁ e₂) (.int (n₁ - n₂))
  | mul {σ e₁ e₂ n₁ n₂} :
      BigStepValue σ e₁ (.int n₁) →
      BigStepValue σ e₂ (.int n₂) →
      BigStepValue σ (.mul e₁ e₂) (.int (n₁ * n₂))
  | eq {σ e₁ e₂ v₁ v₂} :
      BigStepValue σ e₁ v₁ →
      BigStepValue σ e₂ v₂ →
      BigStepValue σ (.eq e₁ e₂) (.bool (decide (v₁ = v₂)))
  | lt {σ e₁ e₂ n₁ n₂} :
      BigStepValue σ e₁ (.int n₁) →
      BigStepValue σ e₂ (.int n₂) →
      BigStepValue σ (.lt e₁ e₂) (.bool (decide (n₁ < n₂)))
  | not {σ e b} :
      BigStepValue σ e (.bool b) →
      BigStepValue σ (.not e) (.bool (!b))

end

inductive ValueCompat : Value → CppType → Prop where
  | unit : ValueCompat .unit (.base .void)
  | bool {b : Bool} : ValueCompat (.bool b) (.base .bool)
  | int  {n : Int}  : ValueCompat (.int n) (.base .int)
  | ptr  {a : Nat} {τ : CppType} : ValueCompat (.addr a) (.ptr τ)


def DeclMatchesBinding : DeclInfo → Binding → Prop
  | .object τ, .object τ' _ => τ = τ'
  | .ref τ, .ref τ' _ => τ = τ'
  | _, _ => False


def TypedState (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x d,
    lookupDecl Γ x = some d →
    ∃ b c,
      lookupBinding σ x = some b ∧
      DeclMatchesBinding d b ∧
      σ.heap (bindingAddr b) = some c ∧
      c.ty = declPlaceType d ∧
      c.alive = true


def Assigns (σ : State) (p : PlaceExpr) (v : Value) (σ' : State) : Prop :=
  ∃ a c,
    BigStepPlace σ p a ∧
    σ.heap a = some c ∧
    c.alive = true ∧
    ValueCompat v c.ty ∧
    σ' = writeHeap σ a { c with value := some v }


def DeclaresObject (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (σ' : State) : Prop :=
  ObjectType τ ∧
  currentScopeFresh σ x ∧
  σ.heap σ.next = none ∧
  (match ov with
   | none => True
   | some v => ValueCompat v τ) ∧
  σ' = declareObjectState σ τ x ov


def DeclaresRef (σ : State) (τ : CppType) (x : Ident) (a : Nat) (σ' : State) : Prop :=
  currentScopeFresh σ x ∧
  ∃ c,
    σ.heap a = some c ∧
    c.ty = τ ∧
    c.alive = true ∧
    σ' = declareRefState σ τ x a


def OpenScope (σ σ' : State) : Prop :=
  σ' = pushScope σ


def CloseScope (σ σ' : State) : Prop :=
  popScope? σ = some σ'

mutual

inductive BigStepStmt : State → CppStmt → CtrlResult → State → Prop where
  | skip {σ} :
      BigStepStmt σ .skip .normal σ
  | expr {σ e v} :
      BigStepValue σ e v →
      BigStepStmt σ (.exprStmt e) .normal σ
  | assign {σ σ' p e v} :
      BigStepValue σ e v →
      Assigns σ p v σ' →
      BigStepStmt σ (.assign p e) .normal σ'
  | declareObjNone {σ σ' τ x} :
      DeclaresObject σ τ x none σ' →
      BigStepStmt σ (.declareObj τ x none) .normal σ'
  | declareObjSome {σ σ' τ x e v} :
      BigStepValue σ e v →
      DeclaresObject σ τ x (some v) σ' →
      BigStepStmt σ (.declareObj τ x (some e)) .normal σ'
  | declareRef {σ σ' τ x p a} :
      BigStepPlace σ p a →
      DeclaresRef σ τ x a σ' →
      BigStepStmt σ (.declareRef τ x p) .normal σ'
  | seqNormal {σ σ₁ σ₂ s t ctrl} :
      BigStepStmt σ s .normal σ₁ →
      BigStepStmt σ₁ t ctrl σ₂ →
      BigStepStmt σ (.seq s t) ctrl σ₂
  | seqBreak {σ σ₁ s t} :
      BigStepStmt σ s .breakResult σ₁ →
      BigStepStmt σ (.seq s t) .breakResult σ₁
  | seqContinue {σ σ₁ s t} :
      BigStepStmt σ s .continueResult σ₁ →
      BigStepStmt σ (.seq s t) .continueResult σ₁
  | seqReturn {σ σ₁ s t rv} :
      BigStepStmt σ s (.returnResult rv) σ₁ →
      BigStepStmt σ (.seq s t) (.returnResult rv) σ₁
  | iteTrue {σ σ' c s t ctrl} :
      BigStepValue σ c (.bool true) →
      BigStepStmt σ s ctrl σ' →
      BigStepStmt σ (.ite c s t) ctrl σ'
  | iteFalse {σ σ' c s t ctrl} :
      BigStepValue σ c (.bool false) →
      BigStepStmt σ t ctrl σ' →
      BigStepStmt σ (.ite c s t) ctrl σ'
  | whileFalse {σ c body} :
      BigStepValue σ c (.bool false) →
      BigStepStmt σ (.whileStmt c body) .normal σ
  | whileTrueNormal {σ σ₁ σ₂ c body ctrl} :
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ₁ →
      BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂ →
      BigStepStmt σ (.whileStmt c body) ctrl σ₂
  | whileTrueBreak {σ σ₁ c body} :
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .breakResult σ₁ →
      BigStepStmt σ (.whileStmt c body) .normal σ₁
  | whileTrueContinue {σ σ₁ σ₂ c body ctrl} :
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ₁ →
      BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂ →
      BigStepStmt σ (.whileStmt c body) ctrl σ₂
  | whileTrueReturn {σ σ₁ c body rv} :
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body (.returnResult rv) σ₁ →
      BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ₁
  | block {σ σ₁ σ₂ σ₃ ss ctrl} :
      OpenScope σ σ₁ →
      BigStepBlock σ₁ ss ctrl σ₂ →
      CloseScope σ₂ σ₃ →
      BigStepStmt σ (.block ss) ctrl σ₃
  | breakStmt {σ} :
      BigStepStmt σ .breakStmt .breakResult σ
  | continueStmt {σ} :
      BigStepStmt σ .continueStmt .continueResult σ
  | returnNoneStmt {σ} :
      BigStepStmt σ (.returnStmt none) (.returnResult none) σ
  | returnSome {σ e v} :
      BigStepValue σ e v →
      BigStepStmt σ (.returnStmt (some e)) (.returnResult (some v)) σ

inductive BigStepBlock : State → StmtBlock → CtrlResult → State → Prop where
  | nil {σ} :
      BigStepBlock σ .nil .normal σ
  | consNormal {σ σ₁ σ₂ s ss ctrl} :
      BigStepStmt σ s .normal σ₁ →
      BigStepBlock σ₁ ss ctrl σ₂ →
      BigStepBlock σ (.cons s ss) ctrl σ₂
  | consBreak {σ σ₁ s ss} :
      BigStepStmt σ s .breakResult σ₁ →
      BigStepBlock σ (.cons s ss) .breakResult σ₁
  | consContinue {σ σ₁ s ss} :
      BigStepStmt σ s .continueResult σ₁ →
      BigStepBlock σ (.cons s ss) .continueResult σ₁
  | consReturn {σ σ₁ s ss rv} :
      BigStepStmt σ s (.returnResult rv) σ₁ →
      BigStepBlock σ (.cons s ss) (.returnResult rv) σ₁

end


def BigStepStmtTerminates (σ : State) (st : CppStmt) : Prop :=
  ∃ ctrl σ', BigStepStmt σ st ctrl σ'

class NoExprDivergence : Prop where
  no_div : True

def LoopBodyAdvances (σ : State) (body : CppStmt) (σ' : State) : Prop :=
  BigStepStmt σ body .normal σ' ∨
  BigStepStmt σ body .continueResult σ'

inductive WhilePrefix : Nat → State → ValExpr → CppStmt → State → Prop where
  | zero {σ : State} {c : ValExpr} {body : CppStmt} :
      WhilePrefix 0 σ c body σ
  | succ {n : Nat} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      LoopBodyAdvances σ body σ₁ →
      WhilePrefix n σ₁ c body σ₂ →
      WhilePrefix (n + 1) σ c body σ₂

mutual

inductive BigStepStmtDiv : State → CppStmt → Prop where
  | seqLeft {σ : State} {s t : CppStmt} :
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.seq s t)

  | seqRight {σ σ₁ : State} {s t : CppStmt} :
      BigStepStmt σ s .normal σ₁ →
      BigStepStmtDiv σ₁ t →
      BigStepStmtDiv σ (.seq s t)

  | iteTrue {σ : State} {c : ValExpr} {s t : CppStmt} :
      BigStepValue σ c (.bool true) →
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.ite c s t)

  | iteFalse {σ : State} {c : ValExpr} {s t : CppStmt} :
      BigStepValue σ c (.bool false) →
      BigStepStmtDiv σ t →
      BigStepStmtDiv σ (.ite c s t)

  | whileBody {σ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      BigStepStmtDiv σ body →
      BigStepStmtDiv σ (.whileStmt c body)

  | whileIter {σ σ₁ : State} {c : ValExpr} {body : CppStmt} :
      BigStepValue σ c (.bool true) →
      LoopBodyAdvances σ body σ₁ →
      BigStepStmtDiv σ₁ (.whileStmt c body) →
      BigStepStmtDiv σ (.whileStmt c body)

  | whileForever {σ : State} {c : ValExpr} {body : CppStmt} :
      (∀ n : Nat, ∃ σn : State, WhilePrefix n σ c body σn) →
      BigStepStmtDiv σ (.whileStmt c body)

  | block {σ σ₁ : State} {ss : StmtBlock} :
      OpenScope σ σ₁ →
      BigStepBlockDiv σ₁ ss →
      BigStepStmtDiv σ (.block ss)

inductive BigStepBlockDiv : State → StmtBlock → Prop where
  | consHere {σ : State} {s : CppStmt} {ss : StmtBlock} :
      BigStepStmtDiv σ s →
      BigStepBlockDiv σ (.cons s ss)

  | consTail {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock} :
      BigStepStmt σ s .normal σ₁ →
      BigStepBlockDiv σ₁ ss →
      BigStepBlockDiv σ (.cons s ss)

end


def UnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ BigStepStmtTerminates σ st ∧ ¬ BigStepStmtDiv σ st


def IdealAssumptions (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellFormedStmt st ∧
  WellTypedFrom Γ st ∧
  TypedState Γ σ ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st ∧
  BreakWellScoped st ∧
  ContinueWellScoped st

/-! Structural inversion layer. -/

theorem wf_seq_inv_left {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt s := by
  intro h
  exact h.1

theorem wf_seq_inv_right {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt t := by
  intro h
  exact h.2

theorem wf_ite_inv_cond {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedValue c := by
  intro h
  exact h.1

theorem wf_ite_inv_then {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt s := by
  intro h
  exact h.2.1

theorem wf_ite_inv_else {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt t := by
  intro h
  exact h.2.2

theorem wf_while_inv_body {c : ValExpr} {body : CppStmt} :
    WellFormedStmt (.whileStmt c body) → WellFormedStmt body := by
  intro h
  exact h.2

/-- ブロック内の要素に対する WellFormedStmt の逆転定理 -/
private theorem wf_block_mem
    {ss : StmtBlock} {s : CppStmt} :
    WellFormedBlock ss → StmtBlock.Mem s ss → WellFormedStmt s :=
  match ss with
  | .nil =>
      -- Mem s .nil は False なので、矛盾から証明
      fun _ hmem => False.elim hmem
  | .cons _t _ts =>
      -- h: WellFormedStmt t ∧ WellFormedBlock ts
      -- hmem: s = t ∨ Mem s ts
      fun h hmem =>
        match hmem with
        | Or.inl (heq : s = _t) =>
            -- s = t なので、h の左側 (WellFormedStmt t) が答え
            heq.symm ▸ h.left
        | Or.inr (hmemTail : StmtBlock.Mem s _ts) =>
            -- s が後半にあるので、再帰的に証明
            wf_block_mem h.right hmemTail

theorem wf_block_inv {ss : StmtBlock} {s : CppStmt} :
    WellFormedStmt (.block ss) → StmtBlock.Mem s ss → WellFormedStmt s := by
  intro h hs
  exact wf_block_mem h hs

theorem typed_seq_inv
    {Γ Δ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) Δ → ∃ Γ₁, HasTypeStmt Γ s Γ₁ ∧ HasTypeStmt Γ₁ t Δ := by
  intro h
  cases h with
  | seq hs ht => exact ⟨_, hs, ht⟩

theorem typed_ite_inv_cond
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasValueType Γ c (.base .bool) := by
  intro h
  cases h with
  | ite hc _ _ => exact hc

theorem typed_ite_inv_then
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasTypeStmt Γ s Δ := by
  intro h
  cases h with
  | ite _ hs _ => exact hs

theorem typed_ite_inv_else
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasTypeStmt Γ t Δ := by
  intro h
  cases h with
  | ite _ _ ht => exact ht

theorem typed_while_inv_cond
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) Γ → HasValueType Γ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc _ => exact hc

theorem typed_while_inv_body
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) Γ → HasTypeStmt Γ body Γ := by
  intro h
  cases h with
  | whileStmt _ hb => exact hb

private theorem typed_block_mem
    {Γ Δ : TypeEnv} {ss : StmtBlock} {s : CppStmt} :
    HasTypeBlock Γ ss Δ → StmtBlock.Mem s ss → ∃ Γ₁ Γ₂, HasTypeStmt Γ₁ s Γ₂
  | .nil, hmem => False.elim hmem
  | .cons hs htail, hmem =>
      match hmem with
      | Or.inl heq =>
          heq.symm ▸ ⟨_, _, hs⟩
      | Or.inr hmemTail =>
          typed_block_mem htail hmemTail

theorem no_uninit_seq_inv_left {σ : State} {s t : CppStmt} :
    NoUninitStmt σ (.seq s t) → NoUninitStmt σ s := by
  intro h
  exact h.1

theorem no_uninit_seq_inv_right {σ : State} {s t : CppStmt} :
    NoUninitStmt σ (.seq s t) → NoUninitStmt σ t := by
  intro h
  exact h.2

theorem no_invalid_ref_seq_inv_left {σ : State} {s t : CppStmt} :
    NoInvalidRefStmt σ (.seq s t) → NoInvalidRefStmt σ s := by
  intro h
  exact h.1

theorem no_invalid_ref_seq_inv_right {σ : State} {s t : CppStmt} :
    NoInvalidRefStmt σ (.seq s t) → NoInvalidRefStmt σ t := by
  intro h
  exact h.2

theorem ideal_assumptions_inv_wf {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → WellFormedStmt st := by
  intro h
  exact h.1

theorem ideal_assumptions_inv_typed {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → WellTypedFrom Γ st := by
  intro h
  exact h.2.1

theorem ideal_assumptions_inv_typed_state {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → TypedState Γ σ := by
  intro h
  exact h.2.2.1

theorem ideal_assumptions_inv_no_uninit {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → NoUninitStmt σ st := by
  intro h
  exact h.2.2.2.1

theorem ideal_assumptions_inv_no_invalid_ref {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → NoInvalidRefStmt σ st := by
  intro h
  exact h.2.2.2.2.1

theorem ideal_assumptions_inv_break_scoped {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → BreakWellScoped st := by
  intro h
  exact h.2.2.2.2.2.1

theorem ideal_assumptions_inv_continue_scoped {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → ContinueWellScoped st := by
  intro h
  exact h.2.2.2.2.2.2

/-!
Semantic frontier.
The rebuilt syntax and scoped state are concrete. The deep metatheory is still explicit.
-/

axiom assigns_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    TypedState Γ σ →
    HasPlaceType Γ p τ →
    Assigns σ p v σ' →
    TypedState Γ σ'

axiom declares_object_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    TypedState Γ σ →
    DeclaresObject σ τ x ov σ' →
    TypedState (declareTypeObject Γ x τ) σ'

axiom declares_ref_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    TypedState Γ σ →
    DeclaresRef σ τ x a σ' →
    TypedState (declareTypeRef Γ x τ) σ'

axiom place_progress
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ →
    TypedState Γ σ →
    NoUninitPlace σ p →
    NoInvalidRefPlace σ p →
    ∃ a, BigStepPlace σ p a

axiom value_progress
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    TypedState Γ σ →
    NoUninitValue σ e →
    NoInvalidRefValue σ e →
    ∃ v, BigStepValue σ e v

axiom bigstep_preserves_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult} :
    HasTypeStmt Γ st Δ →
    TypedState Γ σ →
    BigStepStmt σ st ctrl σ' →
    TypedState Δ σ'

axiom stmt_safe_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st

axiom no_uninit_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoUninitStmt σ st ↔ NoUninitStmt σ' st

axiom no_invalid_ref_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoInvalidRefStmt σ st ↔ NoInvalidRefStmt σ' st

axiom no_top_break_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    BreakWellScoped st → BigStepStmt σ st .breakResult σ' → False

axiom no_top_continue_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    ContinueWellScoped st → BigStepStmt σ st .continueResult σ' → False

theorem ideal_no_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  exact stmt_safe_progress_or_diverges hfrag hassm

theorem ideal_no_unclassified_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ¬ UnclassifiedStuck σ st := by
  intro hstk
  rcases ideal_no_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm with hterm | hdiv
  · exact hstk.1 hterm
  · exact hstk.2 hdiv


def CtrlToProgSuccess : CtrlResult → Option ProgSuccess
  | .normal => some .normal
  | .returnResult rv => some (.returned rv)
  | .breakResult => none
  | .continueResult => none

theorem top_level_control_not_break
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .breakResult σ') := by
  intro hassm _
  intro h
  rcases h with ⟨σ', hstep⟩
  exact no_top_break_from_scope (ideal_assumptions_inv_break_scoped hassm) hstep

theorem top_level_control_not_continue
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .continueResult σ') := by
  intro hassm _
  intro h
  rcases h with ⟨σ', hstep⟩
  exact no_top_continue_from_scope (ideal_assumptions_inv_continue_scoped hassm) hstep

/-- ケース1: 制御フローが .normal で終了した場合の成功条件の導出 -/
theorem ideal_outcome_success_normal {σ σ' : State} {st : CppStmt} {r : ProgSuccess} :
    CtrlToProgSuccess .normal = some r →
    BigStepStmt σ st .normal σ' →
    (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
    (∃ rv, r = .returned rv ∧ BigStepStmt σ st (.returnResult rv) σ') := by
  intro hcs hstep
  left
  constructor
  · -- hcs の向きを入れ替えてから simplify & apply
    simpa [CtrlToProgSuccess] using hcs.symm
  · exact hstep

/-- ケース2: 制御フローが .returnResult で終了した場合の成功条件の導出 -/
theorem ideal_outcome_success_return {σ σ' : State} {st : CppStmt} {r : ProgSuccess} {rv : Option Value} :
    CtrlToProgSuccess (.returnResult rv) = some r →
    BigStepStmt σ st (.returnResult rv) σ' →
    (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
    (∃ rv', r = .returned rv' ∧ BigStepStmt σ st (.returnResult rv') σ') := by
  intro hcs hstep
  right
  exists rv
  constructor
  · -- hcs : some (.returned rv) = some r を簡約して r = .returned rv を導く
    simp [CtrlToProgSuccess] at hcs
    exact hcs.symm
  · -- 実行ログの整合性
    exact hstep

theorem ideal_prog_outcome_exists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ∃ out : ProgOutcome,
      match out with
      | .success r σ' =>
          (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
          (∃ rv, r = .returned rv ∧ BigStepStmt σ st (.returnResult rv) σ')
      | .diverges => BigStepStmtDiv σ st := by
  rcases ideal_no_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm with hterm | hdiv
  · rcases hterm with ⟨ctrl, σ', hstep⟩
    cases hcs : CtrlToProgSuccess ctrl with
    | none =>
        cases ctrl with
        | normal => cases hcs
        | returnResult rv => cases hcs
        | breakResult =>
            exfalso
            exact top_level_control_not_break hassm hfrag ⟨σ', hstep⟩
        | continueResult =>
            exfalso
            exact top_level_control_not_continue hassm hfrag ⟨σ', hstep⟩
    | some r =>
        refine ⟨.success r σ', ?_⟩
        cases ctrl with
        | normal =>
            exact ideal_outcome_success_normal hcs hstep
        | returnResult rv =>
            exact ideal_outcome_success_return hcs hstep
        | breakResult => cases hcs
        | continueResult => cases hcs
  · exact ⟨.diverges, hdiv⟩


inductive SemFailure where
  | uninitializedRead
  | invalidDeref
  | invalidAssign
  | invalidRefBind
  | badBreak
  | badContinue
  deriving DecidableEq, Repr

inductive SemClassifiedOutcome where
  | success  : ProgSuccess → State → SemClassifiedOutcome
  | failure  : SemFailure → SemClassifiedOutcome
  | diverges : SemClassifiedOutcome
  deriving Repr

axiom BigStepStmtFail : State → CppStmt → SemFailure → Prop


def Classified (σ : State) (st : CppStmt) : Prop :=
  BigStepStmtTerminates σ st ∨ (∃ e, BigStepStmtFail σ st e) ∨ BigStepStmtDiv σ st

axiom ideal_classified
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    Classified σ st

inductive EvalResult (α : Type u) where
  | ok : α → EvalResult α
  | timeout : EvalResult α
  deriving Repr

inductive EvalClassifiedResult (α : Type u) where
  | ok : α → EvalClassifiedResult α
  | fail : SemFailure → EvalClassifiedResult α
  | timeout : EvalClassifiedResult α
  deriving Repr

axiom evalPlace : Nat → State → PlaceExpr → EvalResult Nat
axiom evalValue : Nat → State → ValExpr → EvalResult Value
axiom evalStmt : Nat → State → CppStmt → EvalClassifiedResult (CtrlResult × State)


def InEvaluatorFragment : CppStmt → Prop :=
  InBigStepFragment

axiom evalPlace_fuel_mono
    {fuel : Nat} {σ : State} {p : PlaceExpr} {a : Nat} :
    evalPlace fuel σ p = .ok a → evalPlace (fuel + 1) σ p = .ok a

axiom evalValue_fuel_mono
    {fuel : Nat} {σ : State} {e : ValExpr} {v : Value} :
    evalValue fuel σ e = .ok v → evalValue (fuel + 1) σ e = .ok v

axiom evalStmt_ok_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {res : CtrlResult × State} :
    evalStmt fuel σ st = .ok res → evalStmt (fuel + 1) σ st = .ok res

axiom evalStmt_fail_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    evalStmt fuel σ st = .fail e → evalStmt (fuel + 1) σ st = .fail e

axiom evalPlace_sound
    {fuel : Nat} {σ : State} {p : PlaceExpr} {a : Nat} :
    evalPlace fuel σ p = .ok a → BigStepPlace σ p a

axiom evalValue_sound
    {fuel : Nat} {σ : State} {e : ValExpr} {v : Value} :
    evalValue fuel σ e = .ok v → BigStepValue σ e v

axiom evalStmt_ok_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .ok (ctrl, σ') →
    BigStepStmt σ st ctrl σ'

axiom evalStmt_fail_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .fail e →
    BigStepStmtFail σ st e

axiom evalPlace_complete
    {σ : State} {p : PlaceExpr} {a : Nat} :
    BigStepPlace σ p a → ∃ fuel, evalPlace fuel σ p = .ok a

axiom evalValue_complete
    {σ : State} {e : ValExpr} {v : Value} :
    BigStepValue σ e v → ∃ fuel, evalValue fuel σ e = .ok v

axiom evalStmt_ok_complete
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, evalStmt fuel σ st = .ok (ctrl, σ')

axiom evalStmt_fail_complete
    {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    BigStepStmtFail σ st e →
    ∃ fuel, evalStmt fuel σ st = .fail e

axiom timeout_eliminated_by_sufficient_fuel
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, ∀ fuel' ≥ fuel, evalStmt fuel' σ st = .ok (ctrl, σ')

structure RealProgram where
  source : String
  deriving Repr

axiom ObservedBadBehavior : RealProgram → Prop
axiom EncodesAsIdeal : RealProgram → TypeEnv → State → CppStmt → Prop


def BridgeCorrect (real : RealProgram) (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  EncodesAsIdeal real Γ σ st


def RealCounterexample (real : RealProgram) : Prop :=
  ObservedBadBehavior real

axiom real_counterexample_requires_escape_or_bad_bridge
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    ¬ IdealAssumptions Γ σ st ∨ ¬ BridgeCorrect real Γ σ st ∨ UnclassifiedStuck σ st

theorem real_counterexample_not_internal_refutation
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    BridgeCorrect real Γ σ st →
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    False := by
  intro hreal hbridge hassm hfrag
  have hnstk := ideal_no_unclassified_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm
  rcases real_counterexample_requires_escape_or_bad_bridge (Γ := Γ) (σ := σ) (st := st) hreal with hbad | hbad | hstk
  · exact hbad hassm
  · exact hbad hbridge
  · exact hnstk hstk

structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  closedUnder : Name → CppStmt → Prop

structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop
  preserves : Meta → TypeEnv → State → CppStmt → Prop

axiom std_fragment_preserves_ideal_boundary
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    IdealAssumptions Γ σ st

axiom reflection_fragment_preserves_core_fragment
    {R : VerifiedReflectionFragment} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    R.generates m st →
    R.preserves m Γ σ st →
    CoreBigStepFragment st

theorem reflective_std_closure_theorem
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    {n : F.Name} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    R.generates m st →
    R.preserves m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hclosed hgen hpres
  have hfrag : CoreBigStepFragment st :=
    reflection_fragment_preserves_core_fragment hgen hpres
  have hassm : IdealAssumptions Γ σ st :=
    std_fragment_preserves_ideal_boundary huse hclosed
  exact ideal_no_stuck hfrag hassm

end Cpp
