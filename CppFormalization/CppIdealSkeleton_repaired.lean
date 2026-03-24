namespace Cpp

universe u

/-!
This is a repaired contract-level skeleton.
What is actually proved here is only the structural layer.
Everything that genuinely requires a real semantic model is made explicit as an axiom.
That is deliberate: the original file mixed structural facts with statements that are not yet
mathematically provable from the given definitions.
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

inductive Value where
  | unit
  | bool : Bool → Value
  | int  : Int → Value
  | addr : Nat → Value
  deriving DecidableEq, Repr

structure Cell where
  ty    : CppType
  value : Option Value
  alive : Bool
  deriving Repr

structure State where
  vars : Ident → Option Nat
  heap : Nat → Option Cell
  next : Nat

instance : Repr State where
  reprPrec s _ :=
    "State { vars := <fun>, heap := <fun>, next := " ++ repr s.next ++ " }"

def emptyState : State := {
  vars := fun _ => none
  heap := fun _ => none
  next := 0
}

instance : Inhabited State where
  default := emptyState

structure TypeEnv where
  lookup : Ident → Option CppType

inductive CppExpr where
  | litBool : Bool → CppExpr
  | litInt  : Int → CppExpr
  | var     : Ident → CppExpr
  | addrOf  : Ident → CppExpr
  | deref   : CppExpr → CppExpr
  | add     : CppExpr → CppExpr → CppExpr
  | sub     : CppExpr → CppExpr → CppExpr
  | mul     : CppExpr → CppExpr → CppExpr
  | eq      : CppExpr → CppExpr → CppExpr
  | lt      : CppExpr → CppExpr → CppExpr
  | not     : CppExpr → CppExpr
  deriving DecidableEq, Repr

mutual
inductive CppStmt where
  | skip
  | exprStmt   : CppExpr → CppStmt
  | assignVar  : Ident → CppExpr → CppStmt
  | declare    : CppType → Ident → Option CppExpr → CppStmt
  | seq        : CppStmt → CppStmt → CppStmt
  | ite        : CppExpr → CppStmt → CppStmt → CppStmt
  | whileStmt  : CppExpr → CppStmt → CppStmt
  | block      : StmtBlock → CppStmt
  | breakStmt
  | continueStmt
  | returnStmt : Option CppExpr → CppStmt

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
  | .assignVar _ _ => True
  | .declare _ _ _ => True
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

inductive HasTypeExpr : TypeEnv → CppExpr → CppType → Prop where
  | litBool {Γ b} : HasTypeExpr Γ (.litBool b) (.base .bool)
  | litInt  {Γ n} : HasTypeExpr Γ (.litInt n) (.base .int)
  | var     {Γ x τ} : Γ.lookup x = some τ → HasTypeExpr Γ (.var x) τ
  | addrOf  {Γ x τ} : Γ.lookup x = some τ → HasTypeExpr Γ (.addrOf x) (.ptr τ)
  | deref   {Γ e τ} : HasTypeExpr Γ e (.ptr τ) → HasTypeExpr Γ (.deref e) τ
  | add     {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.add e₁ e₂) (.base .int)
  | sub     {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.sub e₁ e₂) (.base .int)
  | mul     {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.mul e₁ e₂) (.base .int)
  | eq      {Γ e₁ e₂ τ} :
      HasTypeExpr Γ e₁ τ →
      HasTypeExpr Γ e₂ τ →
      HasTypeExpr Γ (.eq e₁ e₂) (.base .bool)
  | lt      {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.lt e₁ e₂) (.base .bool)
  | not     {Γ e} :
      HasTypeExpr Γ e (.base .bool) →
      HasTypeExpr Γ (.not e) (.base .bool)

mutual

inductive HasTypeStmt : TypeEnv → CppStmt → Prop where
  | skip {Γ} : HasTypeStmt Γ .skip
  | expr {Γ e τ} : HasTypeExpr Γ e τ → HasTypeStmt Γ (.exprStmt e)
  | assign {Γ x e τ} :
      Γ.lookup x = some τ → HasTypeExpr Γ e τ → HasTypeStmt Γ (.assignVar x e)
  | declare {Γ τ x init} :
      (match init with
       | none => True
       | some e => HasTypeExpr Γ e τ) →
      HasTypeStmt Γ (.declare τ x init)
  | seq {Γ s t} : HasTypeStmt Γ s → HasTypeStmt Γ t → HasTypeStmt Γ (.seq s t)
  | ite {Γ c s t} :
      HasTypeExpr Γ c (.base .bool) →
      HasTypeStmt Γ s →
      HasTypeStmt Γ t →
      HasTypeStmt Γ (.ite c s t)
  | whileStmt {Γ c body} :
      HasTypeExpr Γ c (.base .bool) →
      HasTypeStmt Γ body →
      HasTypeStmt Γ (.whileStmt c body)
  | block {Γ ss} : HasTypeBlock Γ ss → HasTypeStmt Γ (.block ss)
  | breakStmt {Γ} : HasTypeStmt Γ .breakStmt
  | continueStmt {Γ} : HasTypeStmt Γ .continueStmt
  | returnNone {Γ} : HasTypeStmt Γ (.returnStmt none)
  | returnSome {Γ e τ} : HasTypeExpr Γ e τ → HasTypeStmt Γ (.returnStmt (some e))

inductive HasTypeBlock : TypeEnv → StmtBlock → Prop where
  | nil {Γ} : HasTypeBlock Γ .nil
  | cons {Γ s ss} :
      HasTypeStmt Γ s → HasTypeBlock Γ ss → HasTypeBlock Γ (.cons s ss)

end


def TypedState (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x a τ,
    σ.vars x = some a →
    Γ.lookup x = some τ →
    ∃ c, σ.heap a = some c ∧ c.ty = τ

/-!
These two are still deliberately weak at the contract level.
They do not yet inspect expressions deeply; they only give the theorem DAG a place to hang later refinements.
-/
mutual
def NoUninitStmt (σ : State) : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => NoUninitStmt σ s ∧ NoUninitStmt σ t -- σ を渡す
  | .ite _ s t      => NoUninitStmt σ s ∧ NoUninitStmt σ t -- σ を渡す
  | .whileStmt _ b  => NoUninitStmt σ b                 -- σ を渡す
  | .block ss       => NoUninitBlock σ ss               -- σ を渡す
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def NoUninitBlock (σ : State) : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => NoUninitStmt σ s ∧ NoUninitBlock σ ss -- σ を渡す
end

mutual
def NoInvalidRefStmt (σ : State) : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t -- σ を渡す
  | .ite _ s t      => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t -- σ を渡す
  | .whileStmt _ b  => NoInvalidRefStmt σ b                 -- σ を渡す
  | .block ss       => NoInvalidRefBlock σ ss               -- σ を渡す
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def NoInvalidRefBlock (σ : State) : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => NoInvalidRefStmt σ s ∧ NoInvalidRefBlock σ ss -- σ を渡す
end

mutual

def BreakWellScopedAt : Nat → CppStmt → Prop
  | _d, .skip => True
  | _d, .exprStmt _ => True
  | _d, .assignVar _ _ => True
  | _d, .declare _ _ _ => True
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
  | _d, .assignVar _ _ => True
  | _d, .declare _ _ _ => True
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

def WellFormedStmt : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assignVar _ _ => True
  | .declare _ _ _ => True
  | .seq s t => WellFormedStmt s ∧ WellFormedStmt t
  | .ite _ s t => WellFormedStmt s ∧ WellFormedStmt t
  | .whileStmt _ b => WellFormedStmt b
  | .block ss => WellFormedBlock ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True

def WellFormedBlock : StmtBlock → Prop
  | .nil => True
  | .cons s ss => WellFormedStmt s ∧ WellFormedBlock ss

end


def IdealAssumptions (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellFormedStmt st ∧
  HasTypeStmt Γ st ∧
  TypedState Γ σ ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st ∧
  BreakWellScoped st ∧
  ContinueWellScoped st

inductive BigStepExpr : State → CppExpr → Value → Prop where
  | litBool {σ b} : BigStepExpr σ (.litBool b) (.bool b)
  | litInt  {σ n} : BigStepExpr σ (.litInt n) (.int n)
  | var     {σ x a c v} :
      σ.vars x = some a →
      σ.heap a = some c →
      c.value = some v →
      BigStepExpr σ (.var x) v
  | addrOf  {σ x a} :
      σ.vars x = some a →
      BigStepExpr σ (.addrOf x) (.addr a)
  | deref   {σ e a c v} :
      BigStepExpr σ e (.addr a) →
      σ.heap a = some c →
      c.value = some v →
      BigStepExpr σ (.deref e) v
  | add     {σ e₁ e₂ n₁ n₂} :
      BigStepExpr σ e₁ (.int n₁) →
      BigStepExpr σ e₂ (.int n₂) →
      BigStepExpr σ (.add e₁ e₂) (.int (n₁ + n₂))
  | sub     {σ e₁ e₂ n₁ n₂} :
      BigStepExpr σ e₁ (.int n₁) →
      BigStepExpr σ e₂ (.int n₂) →
      BigStepExpr σ (.sub e₁ e₂) (.int (n₁ - n₂))
  | mul     {σ e₁ e₂ n₁ n₂} :
      BigStepExpr σ e₁ (.int n₁) →
      BigStepExpr σ e₂ (.int n₂) →
      BigStepExpr σ (.mul e₁ e₂) (.int (n₁ * n₂))
  | eq      {σ e₁ e₂ v₁ v₂} :
      BigStepExpr σ e₁ v₁ →
      BigStepExpr σ e₂ v₂ →
      BigStepExpr σ (.eq e₁ e₂) (.bool (decide (v₁ = v₂)))
  | lt      {σ e₁ e₂ n₁ n₂} :
      BigStepExpr σ e₁ (.int n₁) →
      BigStepExpr σ e₂ (.int n₂) →
      BigStepExpr σ (.lt e₁ e₂) (.bool (n₁ < n₂))
  | not     {σ e b} :
      BigStepExpr σ e (.bool b) →
      BigStepExpr σ (.not e) (.bool (!b))

axiom Assigns : State → Ident → Value → State → Prop
axiom Declares : State → CppType → Ident → Option Value → State → Prop

inductive BigStepStmt : State → CppStmt → CtrlResult → State → Prop where
  | skip {σ} : BigStepStmt σ .skip .normal σ
  | expr {σ e v} :
      BigStepExpr σ e v →
      BigStepStmt σ (.exprStmt e) .normal σ
  | assign {σ σ' x e v} :
      BigStepExpr σ e v →
      Assigns σ x v σ' →
      BigStepStmt σ (.assignVar x e) .normal σ'
  | declareNone {σ σ' τ x} :
      Declares σ τ x none σ' →
      BigStepStmt σ (.declare τ x none) .normal σ'
  | declareSome {σ σ' τ x e v} :
      BigStepExpr σ e v →
      Declares σ τ x (some v) σ' →
      BigStepStmt σ (.declare τ x (some e)) .normal σ'
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
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ s ctrl σ' →
      BigStepStmt σ (.ite c s t) ctrl σ'
  | iteFalse {σ σ' c s t ctrl} :
      BigStepExpr σ c (.bool false) →
      BigStepStmt σ t ctrl σ' →
      BigStepStmt σ (.ite c s t) ctrl σ'
  | whileFalse {σ c body} :
      BigStepExpr σ c (.bool false) →
      BigStepStmt σ (.whileStmt c body) .normal σ
  | whileTrueNormal {σ σ₁ σ₂ c body ctrl} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body .normal σ₁ →
      BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂ →
      BigStepStmt σ (.whileStmt c body) ctrl σ₂
  | whileTrueBreak {σ σ₁ c body} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body .breakResult σ₁ →
      BigStepStmt σ (.whileStmt c body) .normal σ₁
  | whileTrueContinue {σ σ₁ σ₂ c body ctrl} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body .continueResult σ₁ →
      BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂ →
      BigStepStmt σ (.whileStmt c body) ctrl σ₂
  | whileTrueReturn {σ σ₁ c body rv} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body (.returnResult rv) σ₁ →
      BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ₁
  | blockNil {σ} :
      BigStepStmt σ (.block .nil) .normal σ
  | blockCons {σ σ' s ss ctrl} :
      BigStepStmt σ (.seq s (.block ss)) ctrl σ' →
      BigStepStmt σ (.block (.cons s ss)) ctrl σ'
  | breakStmt {σ} : BigStepStmt σ .breakStmt .breakResult σ
  | continueStmt {σ} : BigStepStmt σ .continueStmt .continueResult σ
  | returnNoneStmt {σ} : BigStepStmt σ (.returnStmt none) (.returnResult none) σ
  | returnSome {σ e v} :
      BigStepExpr σ e v →
      BigStepStmt σ (.returnStmt (some e)) (.returnResult (some v)) σ


def BigStepStmtTerminates (σ : State) (st : CppStmt) : Prop :=
  ∃ ctrl σ', BigStepStmt σ st ctrl σ'

class NoExprDivergence : Prop where
  no_div : True

coinductive BigStepStmtDiv : State → CppStmt → Prop where
  | seq_left {σ s t} :
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.seq s t)
  | seq_right {σ σ₁ s t} :
      BigStepStmt σ s .normal σ₁ →
      BigStepStmtDiv σ₁ t →
      BigStepStmtDiv σ (.seq s t)
  | ite_true {σ c s t} :
      BigStepExpr σ c (.bool true) →
      BigStepStmtDiv σ s →
      BigStepStmtDiv σ (.ite c s t)
  | ite_false {σ c s t} :
      BigStepExpr σ c (.bool false) →
      BigStepStmtDiv σ t →
      BigStepStmtDiv σ (.ite c s t)
  | while_body {σ c body} :
      BigStepExpr σ c (.bool true) →
      BigStepStmtDiv σ body →
      BigStepStmtDiv σ (.whileStmt c body)
  | while_loop {σ σ₁ c body} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body .normal σ₁ →
      BigStepStmtDiv σ₁ (.whileStmt c body) →
      BigStepStmtDiv σ (.whileStmt c body)
  | while_continue {σ σ₁ c body} :
      BigStepExpr σ c (.bool true) →
      BigStepStmt σ body .continueResult σ₁ →
      BigStepStmtDiv σ₁ (.whileStmt c body) →
      BigStepStmtDiv σ (.whileStmt c body)
  | block {σ ss} :
      BigStepStmtDiv σ (.seq (.block ss) .skip) →
      BigStepStmtDiv σ (.block ss)


def UnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ BigStepStmtTerminates σ st ∧ ¬ BigStepStmtDiv σ st

/-! Structural inversion layer. -/

theorem wf_seq_inv_left {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt s := by
  intro h
  exact h.1

theorem wf_seq_inv_right {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt t := by
  intro h
  exact h.2

theorem wf_ite_inv_then {c : CppExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt s := by
  intro h
  exact h.1

theorem wf_ite_inv_else {c : CppExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt t := by
  intro h
  exact h.2

theorem wf_while_inv_body {c : CppExpr} {body : CppStmt} :
    WellFormedStmt (.whileStmt c body) → WellFormedStmt body := by
  intro h
  exact h

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

theorem break_scoped_seq_inv_left {d : Nat} {s t : CppStmt} :
    BreakWellScopedAt d (.seq s t) → BreakWellScopedAt d s := by
  intro h
  exact h.1

theorem break_scoped_seq_inv_right {d : Nat} {s t : CppStmt} :
    BreakWellScopedAt d (.seq s t) → BreakWellScopedAt d t := by
  intro h
  exact h.2

theorem continue_scoped_seq_inv_left {d : Nat} {s t : CppStmt} :
    ContinueWellScopedAt d (.seq s t) → ContinueWellScopedAt d s := by
  intro h
  exact h.1

theorem continue_scoped_seq_inv_right {d : Nat} {s t : CppStmt} :
    ContinueWellScopedAt d (.seq s t) → ContinueWellScopedAt d t := by
  intro h
  exact h.2

theorem typed_seq_inv_left {Γ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) → HasTypeStmt Γ s := by
  intro h
  cases h with
  | seq hs _ => exact hs

theorem typed_seq_inv_right {Γ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) → HasTypeStmt Γ t := by
  intro h
  cases h with
  | seq _ ht => exact ht

theorem typed_ite_inv_cond {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeExpr Γ c (.base .bool) := by
  intro h
  cases h with
  | ite hc _ _ => exact hc

theorem typed_ite_inv_then {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeStmt Γ s := by
  intro h
  cases h with
  | ite _ hs _ => exact hs

theorem typed_ite_inv_else {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeStmt Γ t := by
  intro h
  cases h with
  | ite _ _ ht => exact ht

theorem typed_while_inv_cond {Γ : TypeEnv} {c : CppExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) → HasTypeExpr Γ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc _ => exact hc

theorem typed_while_inv_body {Γ : TypeEnv} {c : CppExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) → HasTypeStmt Γ body := by
  intro h
  cases h with
  | whileStmt _ hb => exact hb

/-- ブロック内の要素に対する HasTypeStmt の逆転定理 -/
private theorem typed_block_mem
    {Γ : TypeEnv} {ss : StmtBlock} {s : CppStmt}
    (h : HasTypeBlock Γ ss) (hmem : StmtBlock.Mem s ss) : HasTypeStmt Γ s :=
  match ss, h with
  | .nil, _ =>
      -- 空のブロックに要素は存在しないため、Mem は False
      False.elim hmem
  | .cons _t _ts, .cons hhead htail =>
      -- hmem は s = t ∨ Mem s ts
      match hmem with
      | Or.inl (heq : s = _t) =>
          -- s = t なので、先頭の型付け証拠 hhead を使う
          heq.symm ▸ hhead
      | Or.inr (hmemTail : StmtBlock.Mem s _ts) =>
          -- s が後半にあるので、再帰的に適用
          typed_block_mem htail hmemTail

theorem typed_block_inv {Γ : TypeEnv} {ss : StmtBlock} {s : CppStmt} :
    HasTypeStmt Γ (.block ss) → StmtBlock.Mem s ss → HasTypeStmt Γ s := by
  intro h hs
  cases h with
  | block hblk => exact typed_block_mem hblk hs

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
    IdealAssumptions Γ σ st → HasTypeStmt Γ st := by
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
Everything below this line depends on the real dynamic model.
The original file treated several of these as if they followed from the earlier definitions, but they do not.
So they are now explicit axioms.
-/

axiom assigns_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {v : Value} :
    TypedState Γ σ → Assigns σ x v σ' → TypedState Γ σ'

axiom declares_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    TypedState Γ σ → Declares σ τ x ov σ' → TypedState Γ σ'

axiom expr_progress
    {Γ : TypeEnv} {σ : State} {e : CppExpr} {τ : CppType} :
    HasTypeExpr Γ e τ →
    TypedState Γ σ →
    NoUninitStmt σ (.exprStmt e) →
    NoInvalidRefStmt σ (.exprStmt e) →
    ∃ v, BigStepExpr σ e v

axiom bigstep_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult} :
    HasTypeStmt Γ st →
    TypedState Γ σ →
    BigStepStmt σ st ctrl σ' →
    TypedState Γ σ'

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

axiom no_top_break_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    BreakWellScoped st → BigStepStmt σ st .breakResult σ' → False

axiom no_top_continue_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    ContinueWellScoped st → BigStepStmt σ st .continueResult σ' → False

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

inductive EvalResult (α : Type u) where
  | ok : α → EvalResult α
  | timeout : EvalResult α
  deriving Repr

axiom evalExpr : Nat → State → CppExpr → EvalResult Value
axiom evalStmt : Nat → State → CppStmt → EvalResult (CtrlResult × State)

def InEvaluatorFragment : CppStmt → Prop :=
  InBigStepFragment

axiom evalExpr_fuel_mono
    {fuel : Nat} {σ : State} {e : CppExpr} {v : Value} :
    evalExpr fuel σ e = .ok v → evalExpr (fuel + 1) σ e = .ok v

axiom evalStmt_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {res : CtrlResult × State} :
    evalStmt fuel σ st = .ok res → evalStmt (fuel + 1) σ st = .ok res

axiom evalExpr_sound
    {fuel : Nat} {σ : State} {e : CppExpr} {v : Value} :
    evalExpr fuel σ e = .ok v → BigStepExpr σ e v

axiom evalStmt_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .ok (ctrl, σ') →
    BigStepStmt σ st ctrl σ'

axiom evalExpr_complete
    {σ : State} {e : CppExpr} {v : Value} :
    BigStepExpr σ e v → ∃ fuel, evalExpr fuel σ e = .ok v

axiom evalStmt_complete
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, evalStmt fuel σ st = .ok (ctrl, σ')

axiom timeout_eliminated_by_sufficient_fuel
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, ∀ fuel' ≥ fuel, evalStmt fuel' σ st = .ok (ctrl, σ')

inductive SemFailure where
  | uninitializedRead
  | invalidDeref
  | invalidAssign
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

axiom fail_soundness
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st → True → BigStepStmtFail σ st e

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
