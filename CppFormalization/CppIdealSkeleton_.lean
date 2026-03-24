namespace Cpp

universe u

/-! # Idealized C++ core: top-down theorem skeleton

This file is intentionally a *design skeleton*.
Every theorem body is `by sorry` on purpose.
The goal is to freeze the dependency DAG from the short-term theorem
`ideal_no_stuck` outward, before any proof engineering starts.
-/

/-- Identifiers for variables / object names in the idealized core. -/
abbrev Ident := String

/-- A minimal collection of base types for the core language. -/
inductive BaseType where
  | void
  | bool
  | int
  deriving DecidableEq, Repr

/-- Core C++ types. Keep intentionally small in the short-term theory. -/
inductive CppType where
  | base   : BaseType → CppType
  | ptr    : CppType → CppType
  | ref    : CppType → CppType
  | array  : CppType → Nat → CppType
  deriving DecidableEq, Repr

/-- Runtime values of the idealized core. -/
inductive Value where
  | unit
  | bool   : Bool → Value
  | int    : Int → Value
  | addr   : Nat → Value
  deriving DecidableEq, Repr

/-- Types of allocated cells in the idealized state. -/
structure Cell where
  ty    : CppType
  value : Option Value
  alive : Bool
  deriving Repr

/-- The idealized runtime state. -/
structure State where
  vars  : Ident → Option Nat
  heap  : Nat → Option Cell
  next  : Nat

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

-- 使うとき
--def s := (default : State)

/-- Static typing environment. -/
structure TypeEnv where
  lookup : Ident → Option CppType

/-- Expression syntax for the core language. -/
inductive CppExpr where
  | litBool   : Bool → CppExpr
  | litInt    : Int → CppExpr
  | var       : Ident → CppExpr
  | addrOf    : Ident → CppExpr
  | deref     : CppExpr → CppExpr
  | add       : CppExpr → CppExpr → CppExpr
  | sub       : CppExpr → CppExpr → CppExpr
  | mul       : CppExpr → CppExpr → CppExpr
  | eq        : CppExpr → CppExpr → CppExpr
  | lt        : CppExpr → CppExpr → CppExpr
  | not       : CppExpr → CppExpr
  deriving DecidableEq, Repr

mutual
/-- Statement syntax for the core language. -/
inductive CppStmt where
  | skip
  | exprStmt      : CppExpr → CppStmt
  | assignVar     : Ident → CppExpr → CppStmt
  | declare       : CppType → Ident → Option CppExpr → CppStmt
  | seq           : CppStmt → CppStmt → CppStmt
  | ite           : CppExpr → CppStmt → CppStmt → CppStmt
  | whileStmt     : CppExpr → CppStmt → CppStmt
  | block         : StmtBlock → CppStmt
  | breakStmt
  | continueStmt
  | returnStmt    : Option CppExpr → CppStmt

/-- Block body as a direct recursive inductive, to keep deriving happy. -/
inductive StmtBlock where
  | nil
  | cons : CppStmt → StmtBlock → StmtBlock
end



def StmtBlock.ofList : List CppStmt → StmtBlock
  | []      => .nil
  | s :: ss => .cons s (ofList ss)

def CppStmt.blockOfList (xs : List CppStmt) : CppStmt :=
  .block (StmtBlock.ofList xs)

def StmtBlock.toList : StmtBlock → List CppStmt
  | .nil => []
  | .cons s ss => s :: toList ss


/-- Statement-level control results. -/
inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnResult  : Option Value → CtrlResult
  deriving DecidableEq, Repr

/-- Program-level successful outcomes only. -/
inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

/-- Program-level outcomes before failure taxonomy is introduced. -/
inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving  Repr

mutual
/-- ステートメントがBig-Step評価の対象フラグメントに含まれるか -/
def InBigStepFragment : CppStmt → Prop
  | .skip                 => True
  | .exprStmt _           => True
  | .assignVar _ _        => True
  | .declare _ _ _        => True
  | .seq s t              => InBigStepFragment s ∧ InBigStepFragment t
  | .ite _ s t            => InBigStepFragment s ∧ InBigStepFragment t
  | .whileStmt _ body     => InBigStepFragment body
  | .block ss             => InBigStepBlockFragment ss  -- 相互再帰呼び出し
  | .breakStmt            => True
  | .continueStmt         => True
  | .returnStmt _         => True

/-- ブロック（ステートメントのリスト）に対する判定 -/
def InBigStepBlockFragment : StmtBlock → Prop
  | .nil         => True
  | .cons s ss   => InBigStepFragment s ∧ InBigStepBlockFragment ss
end

/-- Shorthand name for the short-term fragment theorem assumptions. -/
def CoreBigStepFragment (st : CppStmt) : Prop :=
  InBigStepFragment st

/-! ## Static / local predicates

These are intentionally kept abstract in spirit.  Their theorem skeletons below
force them to behave locally rather than by smuggling whole semantic facts into
one giant predicate.
-/

/-- Expression typing. -/
inductive HasTypeExpr : TypeEnv → CppExpr → CppType → Prop where
  | litBool  {Γ b} : HasTypeExpr Γ (.litBool b) (.base .bool)
  | litInt   {Γ n} : HasTypeExpr Γ (.litInt n) (.base .int)
  | var      {Γ x τ} : Γ.lookup x = some τ → HasTypeExpr Γ (.var x) τ
  | addrOf   {Γ x τ} : Γ.lookup x = some τ → HasTypeExpr Γ (.addrOf x) (.ptr τ)
  | deref    {Γ e τ} : HasTypeExpr Γ e (.ptr τ) → HasTypeExpr Γ (.deref e) τ
  | add      {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.add e₁ e₂) (.base .int)
  | sub      {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.sub e₁ e₂) (.base .int)
  | mul      {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.mul e₁ e₂) (.base .int)
  | eq       {Γ e₁ e₂ τ} :
      HasTypeExpr Γ e₁ τ →
      HasTypeExpr Γ e₂ τ →
      HasTypeExpr Γ (.eq e₁ e₂) (.base .bool)
  | lt       {Γ e₁ e₂} :
      HasTypeExpr Γ e₁ (.base .int) →
      HasTypeExpr Γ e₂ (.base .int) →
      HasTypeExpr Γ (.lt e₁ e₂) (.base .bool)
  | not      {Γ e} :
      HasTypeExpr Γ e (.base .bool) →
      HasTypeExpr Γ (.not e) (.base .bool)

mutual
/-- Statement typing. This is a deliberately compact core judgment.
    Environment evolution is factored into separate skeletons below. -/
inductive HasTypeStmt : TypeEnv → CppStmt → Prop where
  | skip    {Γ} : HasTypeStmt Γ .skip
  | expr    {Γ e τ} : HasTypeExpr Γ e τ → HasTypeStmt Γ (.exprStmt e)
  | assign  {Γ x e τ} :
      Γ.lookup x = some τ → HasTypeExpr Γ e τ → HasTypeStmt Γ (.assignVar x e)
  | declare {Γ τ x init} :
      (match init with
       | none   => True
       | some e => HasTypeExpr Γ e τ) →
      HasTypeStmt Γ (.declare τ x init)
  | seq     {Γ s t} :
      HasTypeStmt Γ s → HasTypeStmt Γ t → HasTypeStmt Γ (.seq s t)
  | ite     {Γ c s t} :
      HasTypeExpr Γ c (.base .bool) →
      HasTypeStmt Γ s →
      HasTypeStmt Γ t →
      HasTypeStmt Γ (.ite c s t)
  | whileStmt   {Γ c body} :
      HasTypeExpr Γ c (.base .bool) →
      HasTypeStmt Γ body →
      HasTypeStmt Γ (.whileStmt c body)
  | block   {Γ ss} :
      HasTypeBlock Γ ss → HasTypeStmt Γ (.block ss) -- 補助述語を使用
  | breakStmt   {Γ} : HasTypeStmt Γ .breakStmt
  | continueStmt {Γ} : HasTypeStmt Γ .continueStmt
  | returnNone {Γ} : HasTypeStmt Γ (.returnStmt none)
  | returnSome {Γ e τ} : HasTypeExpr Γ e τ → HasTypeStmt Γ (.returnStmt (some e))

/-- ブロック（ステートメントのリスト）の型付け規則 -/
inductive HasTypeBlock : TypeEnv → StmtBlock → Prop where
  | nil  {Γ} : HasTypeBlock Γ .nil
  | cons {Γ s ss} :
      HasTypeStmt Γ s → HasTypeBlock Γ ss → HasTypeBlock Γ (.cons s ss)
end

/-- The runtime state respects the current type environment. -/
def TypedState (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x a τ,
    σ.vars x = some a →
    Γ.lookup x = some τ →
    ∃ c, σ.heap a = some c ∧ c.ty = τ

mutual
/-- No read in the statement will require an uninitialized value from the current state.
    This is intended to be local and state-sensitive. -/
def NoUninitStmt (σ : State) : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .ite _ s t      => NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .whileStmt _ b  => NoUninitStmt σ b
  | .block ss       => NoUninitBlock σ ss
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def NoUninitBlock (σ : State) : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => NoUninitStmt σ s ∧ NoUninitBlock σ ss
end


mutual
/-- No invalid reference / dereference obligation is present at the current state. -/
def NoInvalidRefStmt (σ : State) : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .ite _ s t      => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .whileStmt _ b  => NoInvalidRefStmt σ b
  | .block ss       => NoInvalidRefBlock σ ss
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def NoInvalidRefBlock (σ : State) : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => NoInvalidRefStmt σ s ∧ NoInvalidRefBlock σ ss
end

mutual
/-- `break` is used only where it is contextually legal. -/
def BreakWellScoped : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => BreakWellScoped s ∧ BreakWellScoped t
  | .ite _ s t      => BreakWellScoped s ∧ BreakWellScoped t
  | .whileStmt _ b  => BreakWellScoped b
  | .block ss       => BreakWellScopedBlock ss
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def BreakWellScopedBlock : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => BreakWellScoped s ∧ BreakWellScopedBlock ss
end

mutual
/-- `continue` is used only where it is contextually legal. -/
def ContinueWellScoped : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => ContinueWellScoped s ∧ ContinueWellScoped t
  | .ite _ s t      => ContinueWellScoped s ∧ ContinueWellScoped t
  | .whileStmt _ b  => ContinueWellScoped b
  | .block ss       => ContinueWellScopedBlock ss
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def ContinueWellScopedBlock : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => ContinueWellScoped s ∧ ContinueWellScopedBlock ss
end

mutual
/-- Syntactic well-formedness for statements. -/
def WellFormedStmt : CppStmt → Prop
  | .skip           => True
  | .exprStmt _     => True
  | .assignVar _ _  => True
  | .declare _ _ _  => True
  | .seq s t        => WellFormedStmt s ∧ WellFormedStmt t
  | .ite _ s t      => WellFormedStmt s ∧ WellFormedStmt t
  | .whileStmt _ b  => WellFormedStmt b
  | .block ss       => WellFormedBlock ss
  | .breakStmt      => True
  | .continueStmt   => True
  | .returnStmt _   => True

def WellFormedBlock : StmtBlock → Prop
  | .nil           => True
  | .cons s ss     => WellFormedStmt s ∧ WellFormedBlock ss
end

/-- The bundled assumptions of the short-term theorem. -/
def IdealAssumptions (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellFormedStmt st ∧
  HasTypeStmt Γ st ∧
  TypedState Γ σ ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st ∧
  BreakWellScoped st ∧
  ContinueWellScoped st

/-! ## Reference semantics skeleton -/

/-- Expression big-step evaluation. -/
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

/-- State update after assignment. Abstracted as a relation to keep the skeleton flexible. -/
def Assigns (_σ : State) (_x : Ident) (_v : Value) (_σ' : State) : Prop :=
  True

/-- State update after declaration. Abstracted as a relation to keep the skeleton flexible. -/
def Declares (_σ : State) (_τ : CppType) (_x : Ident) (_init : Option Value) (_σ' : State) : Prop :=
  True

/-- Statement big-step evaluation. -/
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

/-- Program-level successful termination extracted from statement big-step. -/
def BigStepProgTerminates (σ : State) (st : CppStmt) : Prop :=
  (∃ σ', BigStepStmt σ st .normal σ') ∨
  (∃ rv σ', BigStepStmt σ st (.returnResult rv) σ')

/-- Statement termination in the weaker internal sense. -/
def BigStepStmtTerminates (σ : State) (st : CppStmt) : Prop :=
  ∃ ctrl σ', BigStepStmt σ st ctrl σ'

/-- Divergence of expressions is not modeled in the short-term fragment. -/
class NoExprDivergence : Prop where
  no_div : True

/-- Coinductive divergence for statements. -/
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

/-- Internal notion of semantic hole: neither finite execution nor divergence. -/
def UnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ BigStepStmtTerminates σ st ∧ ¬ BigStepStmtDiv σ st

/-! ## Inversion / decomposition layer

These are the bottom lemmas: purely structural facts about the vocabulary.
-/

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

 theorem wf_block_inv {ss : List CppStmt} {s : CppStmt} :
    WellFormedStmt (.block ss) → s ∈ ss → WellFormedStmt s := by
  intro h hs
  exact h s hs

 theorem break_scoped_seq_inv_left {s t : CppStmt} :
    BreakWellScoped (.seq s t) → BreakWellScoped s := by
  intro h
  exact h.1

 theorem break_scoped_seq_inv_right {s t : CppStmt} :
    BreakWellScoped (.seq s t) → BreakWellScoped t := by
  intro h
  exact h.2

 theorem continue_scoped_seq_inv_left {s t : CppStmt} :
    ContinueWellScoped (.seq s t) → ContinueWellScoped s := by
  intro h
  exact h.1

 theorem continue_scoped_seq_inv_right {s t : CppStmt} :
    ContinueWellScoped (.seq s t) → ContinueWellScoped t := by
  intro h
  exact h.2

 theorem typed_seq_inv_left {Γ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) → HasTypeStmt Γ s := by
  intro h
  cases h with
  | seq hs ht => exact hs

 theorem typed_seq_inv_right {Γ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) → HasTypeStmt Γ t := by
  intro h
  cases h with
  | seq hs ht => exact ht

 theorem typed_ite_inv_cond {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeExpr Γ c (.base .bool) := by
  intro h
  cases h with
  | ite hc hs ht => exact hc

 theorem typed_ite_inv_then {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeStmt Γ s := by
  intro h
  cases h with
  | ite hc hs ht => exact hs

 theorem typed_ite_inv_else {Γ : TypeEnv} {c : CppExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) → HasTypeStmt Γ t := by
  intro h
  cases h with
  | ite hc hs ht => exact ht

 theorem typed_while_inv_cond {Γ : TypeEnv} {c : CppExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) → HasTypeExpr Γ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc hb => exact hc

 theorem typed_while_inv_body {Γ : TypeEnv} {c : CppExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) → HasTypeStmt Γ body := by
  intro h
  cases h with
  | whileStmt hc hb => exact hb

 theorem typed_block_inv {Γ : TypeEnv} {ss : List CppStmt} {s : CppStmt} :
    HasTypeStmt Γ (.block ss) → s ∈ ss → HasTypeStmt Γ s := by
  intro h hs
  cases h with
  | block hmem => exact hmem s hs


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

/-! ## Local preservation / compatibility layer -/

theorem assigns_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {v : Value} :
    TypedState Γ σ → Assigns σ x v σ' → TypedState Γ σ' := by
  intro hty hassign
  sorry

 theorem declares_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    TypedState Γ σ → Declares σ τ x ov σ' → TypedState Γ σ' := by
  intro hty hdecl
  sorry

 theorem expr_bigstep_preserves_state
    {σ : State} {e : CppExpr} {v : Value} :
    BigStepExpr σ e v → σ = σ := by
  intro h
  rfl

 theorem no_uninit_preserved_by_assign
    {σ σ' : State} {x : Ident} {e : CppExpr} {v : Value} :
    NoUninitStmt σ (.assignVar x e) →
    BigStepExpr σ e v →
    Assigns σ x v σ' →
    NoUninitStmt σ' .skip := by
  intro hnu he hassign
  trivial

 theorem no_invalid_ref_preserved_by_assign
    {σ σ' : State} {x : Ident} {e : CppExpr} {v : Value} :
    NoInvalidRefStmt σ (.assignVar x e) →
    BigStepExpr σ e v →
    Assigns σ x v σ' →
    NoInvalidRefStmt σ' .skip := by
  intro hnr he hassign
  trivial

 theorem break_scoped_preserved_under_substmt
    {s t : CppStmt} :
    BreakWellScoped (.seq s t) → BreakWellScoped s ∧ BreakWellScoped t := by
  intro h
  exact h

 theorem continue_scoped_preserved_under_substmt
    {s t : CppStmt} :
    ContinueWellScoped (.seq s t) → ContinueWellScoped s ∧ ContinueWellScoped t := by
  intro h
  exact h

/-! ## Constructor-level progress / divergence lemmas

These are the middle layer directly feeding the main induction.
-/

theorem skip_progress_or_diverges
    {Γ : TypeEnv} {σ : State} :
    CoreBigStepFragment .skip →
    IdealAssumptions Γ σ .skip →
    BigStepStmtTerminates σ .skip ∨ BigStepStmtDiv σ .skip := by
  intro hfrag hassm
  left
  exact ⟨.normal, σ, BigStepStmt.skip⟩

 theorem expr_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {e : CppExpr} :
    CoreBigStepFragment (.exprStmt e) →
    IdealAssumptions Γ σ (.exprStmt e) →
    BigStepStmtTerminates σ (.exprStmt e) ∨ BigStepStmtDiv σ (.exprStmt e) := by
  intro hfrag hassm
  sorry

 theorem assign_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {x : Ident} {e : CppExpr} :
    CoreBigStepFragment (.assignVar x e) →
    IdealAssumptions Γ σ (.assignVar x e) →
    BigStepStmtTerminates σ (.assignVar x e) ∨ BigStepStmtDiv σ (.assignVar x e) := by
  intro hfrag hassm
  sorry

 theorem declare_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} {init : Option CppExpr} :
    CoreBigStepFragment (.declare τ x init) →
    IdealAssumptions Γ σ (.declare τ x init) →
    BigStepStmtTerminates σ (.declare τ x init) ∨ BigStepStmtDiv σ (.declare τ x init) := by
  intro hfrag hassm
  sorry

 theorem break_progress_or_diverges
    {Γ : TypeEnv} {σ : State} :
    CoreBigStepFragment .breakStmt →
    IdealAssumptions Γ σ .breakStmt →
    BigStepStmtTerminates σ .breakStmt ∨ BigStepStmtDiv σ .breakStmt := by
  intro hfrag hassm
  left
  exact ⟨.breakResult, σ, BigStepStmt.breakStmt⟩

 theorem continue_progress_or_diverges
    {Γ : TypeEnv} {σ : State} :
    CoreBigStepFragment .continueStmt →
    IdealAssumptions Γ σ .continueStmt →
    BigStepStmtTerminates σ .continueStmt ∨ BigStepStmtDiv σ .continueStmt := by
  intro hfrag hassm
  left
  exact ⟨.continueResult, σ, BigStepStmt.continueStmt⟩

 theorem return_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {oe : Option CppExpr} :
    CoreBigStepFragment (.returnStmt oe) →
    IdealAssumptions Γ σ (.returnStmt oe) →
    BigStepStmtTerminates σ (.returnStmt oe) ∨ BigStepStmtDiv σ (.returnStmt oe) := by
  intro hfrag hassm
  sorry

 theorem seq_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    CoreBigStepFragment (.seq s t) →
    IdealAssumptions Γ σ (.seq s t) →
    (BigStepStmtTerminates σ s ∨ BigStepStmtDiv σ s) →
    (∀ σ₁, BigStepStmt σ s .normal σ₁ → BigStepStmtTerminates σ₁ t ∨ BigStepStmtDiv σ₁ t) →
    BigStepStmtTerminates σ (.seq s t) ∨ BigStepStmtDiv σ (.seq s t) := by
  intro hfrag hassm hs hcont
  sorry

 theorem ite_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {c : CppExpr} {s t : CppStmt} :
    CoreBigStepFragment (.ite c s t) →
    IdealAssumptions Γ σ (.ite c s t) →
    (BigStepStmtTerminates σ s ∨ BigStepStmtDiv σ s) →
    (BigStepStmtTerminates σ t ∨ BigStepStmtDiv σ t) →
    BigStepStmtTerminates σ (.ite c s t) ∨ BigStepStmtDiv σ (.ite c s t) := by
  intro hfrag hassm hs ht
  sorry

 theorem while_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {c : CppExpr} {body : CppStmt} :
    CoreBigStepFragment (.whileStmt c body) →
    IdealAssumptions Γ σ (.whileStmt c body) →
    (∀ σ₁, BigStepStmt σ₁ body .normal σ₁ →
      BigStepStmtTerminates σ₁ (.whileStmt c body) ∨ BigStepStmtDiv σ₁ (.whileStmt c body)) →
    (BigStepStmtTerminates σ body ∨ BigStepStmtDiv σ body) →
    BigStepStmtTerminates σ (.whileStmt c body) ∨ BigStepStmtDiv σ (.whileStmt c body) := by
  intro hfrag hassm hrec hbody
  sorry

 theorem block_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    CoreBigStepFragment (.block ss) →
    IdealAssumptions Γ σ (.block ss) →
    BigStepStmtTerminates σ (.block ss) ∨ BigStepStmtDiv σ (.block ss) := by
  intro hfrag hassm
  sorry

/-! ## Main reference-semantics induction layer -/

theorem bigstep_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult} :
    HasTypeStmt Γ st →
    TypedState Γ σ →
    BigStepStmt σ st ctrl σ' →
    TypedState Γ σ' := by
  intro hty hts hstep
  sorry

theorem no_uninit_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoUninitStmt σ st ↔ NoUninitStmt σ' st := by
  induction st with
  | skip => simp [NoUninitStmt]
  | exprStmt e => simp [NoUninitStmt]
  | assignVar x e => simp [NoUninitStmt]
  | declare τ x init => simp [NoUninitStmt]
  | seq s t ihs iht => simp [NoUninitStmt, ihs, iht]
  | ite c s t ihs iht => simp [NoUninitStmt, ihs, iht]
  | whileStmt c body ih => simp [NoUninitStmt, ih]
  | block ss =>
      -- ここは block 側の対応補題が要る
      sorry
  | breakStmt => simp [NoUninitStmt]
  | continueStmt => simp [NoUninitStmt]
  | returnStmt oe => simp [NoUninitStmt]

theorem no_invalid_ref_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoInvalidRefStmt σ st ↔ NoInvalidRefStmt σ' st := by
  induction st with
  | skip => simp [NoInvalidRefStmt]
  | exprStmt e => simp [NoInvalidRefStmt]
  | assignVar x e => simp [NoInvalidRefStmt]
  | declare τ x init => simp [NoInvalidRefStmt]
  | seq s t ihs iht => simp [NoInvalidRefStmt, ihs, iht]
  | ite c s t ihs iht => simp [NoInvalidRefStmt, ihs, iht]
  | whileStmt c body ih => simp [NoInvalidRefStmt, ih]
  | block ss =>
      -- ここも block 側の対応補題が要る
      sorry
  | breakStmt => simp [NoInvalidRefStmt]
  | continueStmt => simp [NoInvalidRefStmt]
  | returnStmt oe => simp [NoInvalidRefStmt]

theorem stmt_safe_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hassm
  cases st with
  | skip =>
      exact skip_progress_or_diverges hfrag hassm
  | exprStmt e =>
      exact expr_progress_or_diverges hfrag hassm
  | assignVar x e =>
      exact assign_progress_or_diverges hfrag hassm
  | declare τ x init =>
      exact declare_progress_or_diverges hfrag hassm
  | seq s t =>
      refine seq_progress_or_diverges hfrag hassm ?_ ?_
      · exact stmt_safe_progress_or_diverges
          (st := s)
          (by
            have h : InBigStepFragment s ∧ InBigStepFragment t := by
              simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
            exact h.1)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact wf_seq_inv_left (ideal_assumptions_inv_wf hassm)
            · exact typed_seq_inv_left (ideal_assumptions_inv_typed hassm)
            · exact ideal_assumptions_inv_typed_state hassm
            · exact no_uninit_seq_inv_left (ideal_assumptions_inv_no_uninit hassm)
            · exact no_invalid_ref_seq_inv_left (ideal_assumptions_inv_no_invalid_ref hassm)
            · exact break_scoped_seq_inv_left (ideal_assumptions_inv_break_scoped hassm)
            · exact continue_scoped_seq_inv_left (ideal_assumptions_inv_continue_scoped hassm))
      · intro σ₁ hs
        exact stmt_safe_progress_or_diverges
          (st := t)
          (by
            have h : InBigStepFragment s ∧ InBigStepFragment t := by
              simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
            exact h.2)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact wf_seq_inv_right (ideal_assumptions_inv_wf hassm)
            · exact typed_seq_inv_right (ideal_assumptions_inv_typed hassm)
            · exact bigstep_preserves_typed_state
                (typed_seq_inv_left (ideal_assumptions_inv_typed hassm))
                (ideal_assumptions_inv_typed_state hassm)
                hs
            ·
              have h0 := no_uninit_seq_inv_right (ideal_assumptions_inv_no_uninit hassm)
              exact (no_uninit_state_irrel (σ := σ) (σ' := σ₁) (st := t)).mp h0
            ·
              have h0 := no_invalid_ref_seq_inv_right (ideal_assumptions_inv_no_invalid_ref hassm)
              exact (no_invalid_ref_state_irrel (σ := σ) (σ' := σ₁) (st := t)).mp h0
            · exact break_scoped_seq_inv_right (ideal_assumptions_inv_break_scoped hassm)
            · exact continue_scoped_seq_inv_right (ideal_assumptions_inv_continue_scoped hassm))
  | ite c s t =>
      refine ite_progress_or_diverges hfrag hassm
        (stmt_safe_progress_or_diverges
          (st := s)
          (by
            have h : InBigStepFragment s ∧ InBigStepFragment t := by
              simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
            exact h.1)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact wf_ite_inv_then (ideal_assumptions_inv_wf hassm)
            · exact typed_ite_inv_then (ideal_assumptions_inv_typed hassm)
            · exact ideal_assumptions_inv_typed_state hassm
            · exact (ideal_assumptions_inv_no_uninit hassm).1
            · exact (ideal_assumptions_inv_no_invalid_ref hassm).1
            · exact (ideal_assumptions_inv_break_scoped hassm).1
            · exact (ideal_assumptions_inv_continue_scoped hassm).1))
        (stmt_safe_progress_or_diverges
          (st := t)
          (by
            have h : InBigStepFragment s ∧ InBigStepFragment t := by
              simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
            exact h.2)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact wf_ite_inv_else (ideal_assumptions_inv_wf hassm)
            · exact typed_ite_inv_else (ideal_assumptions_inv_typed hassm)
            · exact ideal_assumptions_inv_typed_state hassm
            · exact (ideal_assumptions_inv_no_uninit hassm).2
            · exact (ideal_assumptions_inv_no_invalid_ref hassm).2
            · exact (ideal_assumptions_inv_break_scoped hassm).2
            · exact (ideal_assumptions_inv_continue_scoped hassm).2))
  | whileStmt c body =>
      refine while_progress_or_diverges hfrag hassm ?_ ?_
      · intro σ₁ hbody
        exact stmt_safe_progress_or_diverges
          (st := .whileStmt c body)
          (by simpa [CoreBigStepFragment, InBigStepFragment] using hfrag)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact ideal_assumptions_inv_wf hassm
            · exact ideal_assumptions_inv_typed hassm
            · exact bigstep_preserves_typed_state
                (typed_while_inv_body (ideal_assumptions_inv_typed hassm))
                (ideal_assumptions_inv_typed_state hassm)
                hbody
            ·
              have h0 : NoUninitStmt σ (.whileStmt c body) := ideal_assumptions_inv_no_uninit hassm
              exact (no_uninit_state_irrel (σ := σ) (σ' := σ₁) (st := .whileStmt c body)).mp h0
            ·
              have h0 : NoInvalidRefStmt σ (.whileStmt c body) := ideal_assumptions_inv_no_invalid_ref hassm
              exact (no_invalid_ref_state_irrel (σ := σ) (σ' := σ₁) (st := .whileStmt c body)).mp h0
            · exact ideal_assumptions_inv_break_scoped hassm
            · exact ideal_assumptions_inv_continue_scoped hassm)
      · exact stmt_safe_progress_or_diverges
          (st := body)
          (by simpa [CoreBigStepFragment, InBigStepFragment] using hfrag)
          (by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact wf_while_inv_body (ideal_assumptions_inv_wf hassm)
            · exact typed_while_inv_body (ideal_assumptions_inv_typed hassm)
            · exact ideal_assumptions_inv_typed_state hassm
            · exact ideal_assumptions_inv_no_uninit hassm
            · exact ideal_assumptions_inv_no_invalid_ref hassm
            · exact ideal_assumptions_inv_break_scoped hassm
            · exact ideal_assumptions_inv_continue_scoped hassm)
  | block ss =>
      exact block_progress_or_diverges hfrag hassm
  | breakStmt =>
      exact break_progress_or_diverges hfrag hassm
  | continueStmt =>
      exact continue_progress_or_diverges hfrag hassm
  | returnStmt oe =>
      exact return_progress_or_diverges hfrag hassm
termination_by sizeOf st
decreasing_by
  all_goals simp_wf

/-! ## Short-term main theorems -/

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

/-! ## Whole-program projection layer

This keeps statement-level control separate from top-level outcomes.
-/

def CtrlToProgSuccess : CtrlResult → Option ProgSuccess
  | .normal     => some .normal
  | .returnResult rv  => some (.returned rv)
  | .breakResult      => none
  | .continueResult   => none

 theorem top_level_control_not_break
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .breakResult σ') := by
  intro hassm hfrag
  sorry

 theorem top_level_control_not_continue
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    ¬ (∃ σ', BigStepStmt σ st .continueResult σ') := by
  intro hassm hfrag
  sorry

 theorem ideal_prog_outcome_exists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ∃ out : ProgOutcome,
      match out with
      | .success r σ' =>
          (r = .normal ∧ BigStepStmt σ st .normal σ') ∨
          (∃ rv, r = .returned rv ∧ BigStepStmt σ st (.returnResult rv) σ')
      | .diverges     => BigStepStmtDiv σ st := by
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
            left
            exact ⟨by simpa [CtrlToProgSuccess] using hcs, by simpa using hstep⟩
        | breakResult => cases hcs
        | continueResult => cases hcs
        | returnResult rv =>
            right
            refine ⟨rv, ?_, ?_⟩ <;> simpa [CtrlToProgSuccess] using hcs <;> simpa using hstep
  · exact ⟨.diverges, hdiv⟩

/-! ## Second-stage evaluator layer (still skeleton only)

This is intentionally separated from the short-term DAG.
-/

inductive EvalResult (α : Type u) where
  | ok      : α → EvalResult α
  | timeout : EvalResult α
  deriving Repr

/-- A fuel-based evaluator for expressions, kept abstract here. -/
def evalExpr (fuel : Nat) (σ : State) (e : CppExpr) : EvalResult Value :=
  .timeout

/-- A fuel-based evaluator for statements, kept abstract here. -/
def evalStmt (fuel : Nat) (σ : State) (st : CppStmt) : EvalResult (CtrlResult × State) :=
  .timeout

/-- Evaluator fragment, kept separate from the reference-semantics fragment. -/
def InEvaluatorFragment : CppStmt → Prop :=
  InBigStepFragment

 theorem evalExpr_fuel_mono
    {fuel : Nat} {σ : State} {e : CppExpr} {v : Value} :
    evalExpr fuel σ e = .ok v → evalExpr (fuel + 1) σ e = .ok v := by
  intro h
  sorry

 theorem evalStmt_fuel_mono
    {fuel : Nat} {σ : State} {st : CppStmt} {res : CtrlResult × State} :
    evalStmt fuel σ st = .ok res → evalStmt (fuel + 1) σ st = .ok res := by
  intro h
  sorry

 theorem evalExpr_sound
    {fuel : Nat} {σ : State} {e : CppExpr} {v : Value} :
    evalExpr fuel σ e = .ok v → BigStepExpr σ e v := by
  intro h
  sorry

 theorem evalStmt_sound
    {fuel : Nat} {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    evalStmt fuel σ st = .ok (ctrl, σ') →
    BigStepStmt σ st ctrl σ' := by
  intro hfrag h
  sorry

 theorem evalExpr_complete
    {σ : State} {e : CppExpr} {v : Value} :
    BigStepExpr σ e v → ∃ fuel, evalExpr fuel σ e = .ok v := by
  intro h
  sorry

 theorem evalStmt_complete
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, evalStmt fuel σ st = .ok (ctrl, σ') := by
  intro hfrag h
  sorry

 theorem timeout_eliminated_by_sufficient_fuel
    {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State} :
    InEvaluatorFragment st →
    BigStepStmt σ st ctrl σ' →
    ∃ fuel, ∀ fuel' ≥ fuel, evalStmt fuel' σ st = .ok (ctrl, σ') := by
  intro hfrag h
  sorry

/-! ## Third-stage failure taxonomy layer -/

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
  deriving  Repr

/-- Failure semantics relation, intentionally abstract for the staged design. -/
def BigStepStmtFail (σ : State) (st : CppStmt) (e : SemFailure) : Prop :=
  True

/-- Classified execution: later extension of the short-term theorem. -/
def Classified (σ : State) (st : CppStmt) : Prop :=
  BigStepStmtTerminates σ st ∨ (∃ e, BigStepStmtFail σ st e) ∨ BigStepStmtDiv σ st

 theorem ideal_classified
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    WellFormedStmt st →
    HasTypeStmt Γ st →
    TypedState Γ σ →
    Classified σ st := by
  intro hfrag hwf hty hstate
  sorry

 theorem fail_soundness
    {fuel : Nat} {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    True →
    BigStepStmtFail σ st e := by
  intro hfrag hev
  sorry

 theorem fail_completeness
    {σ : State} {st : CppStmt} {e : SemFailure} :
    InEvaluatorFragment st →
    BigStepStmtFail σ st e →
    ∃ fuel : Nat, True := by
  intro hfrag hfail
  sorry

/-! ## Fourth-stage bridge layer

This is deliberately external to the short-term theorem itself.
-/

/-- Placeholder for a real external C++ artifact. -/
structure RealProgram where
  source : String
  deriving Repr

/-- External bad behavior observation. -/
def ObservedBadBehavior (_real : RealProgram) : Prop :=
  True

/-- The bridge from an external artifact into the idealized model. -/
def EncodesAsIdeal (_real : RealProgram) (_Γ : TypeEnv) (_σ : State) (_st : CppStmt) : Prop :=
  True

/-- Short name for bridge correctness. -/
def BridgeCorrect (real : RealProgram) (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  EncodesAsIdeal real Γ σ st

/-- External counterexample notion. -/
def RealCounterexample (real : RealProgram) : Prop :=
  ObservedBadBehavior real

 theorem real_counterexample_requires_escape_or_bad_bridge
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    ¬ IdealAssumptions Γ σ st ∨ ¬ BridgeCorrect real Γ σ st ∨ UnclassifiedStuck σ st := by
  intro hreal
  sorry

 theorem real_counterexample_not_internal_refutation
    {real : RealProgram} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    RealCounterexample real →
    BridgeCorrect real Γ σ st →
    IdealAssumptions Γ σ st →
    CoreBigStepFragment st →
    False := by
  intro hreal hbridge hassm hfrag
  have hnstk := ideal_no_unclassified_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm
  sorry

/-! ## Fifth-stage forward-extension hooks for std / reflection

These are only hooks.  They deliberately do not contaminate the short-term DAG.
-/

/-- A verified std fragment is a collection of library features proved to preserve the core boundary. -/
structure VerifiedStdFragment where
  Name        : Type
  uses        : Name → Prop
  closedUnder : Name → CppStmt → Prop

/-- A verified reflection fragment describes which reflective generators are admitted. -/
structure VerifiedReflectionFragment where
  Meta        : Type
  generates   : Meta → CppStmt → Prop
  preserves   : Meta → TypeEnv → State → CppStmt → Prop

 theorem std_fragment_preserves_ideal_boundary
    {F : VerifiedStdFragment} {n : F.Name} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    F.uses n →
    F.closedUnder n st →
    IdealAssumptions Γ σ st := by
  intro huse hclosed
  sorry

 theorem reflection_fragment_preserves_core_fragment
    {R : VerifiedReflectionFragment} {m : R.Meta} {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    R.generates m st →
    R.preserves m Γ σ st →
    CoreBigStepFragment st := by
  intro hgen hpres
  sorry

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
