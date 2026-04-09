import CppFormalization.Cpp2.Semantics.Expr
import CppFormalization.Cpp2.Core.RuntimeState
import CppFormalization.Cpp2.Core.RuntimeObjectCore
import CppFormalization.Cpp2.Core.Syntax
import CppFormalization.Cpp2.Core.Types
import CppFormalization.Cpp2.Core.Outcome

/-!
Concrete statement and block semantics.
-/

namespace Cpp

def Assigns (σ : State) (p : PlaceExpr) (v : Value) (σ' : State) : Prop :=
  ∃ a c,
    BigStepPlace σ p a ∧
    σ.heap a = some c ∧
    c.alive = true ∧
    ValueCompat v c.ty ∧
    σ' = writeHeap σ a { c with value := some v }


def DeclaresObjectWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (aNext : Nat) (σ' : State) : Prop :=
  ObjectType τ ∧
  currentScopeFresh σ x ∧
  σ.heap σ.next = none ∧
  (match ov with
   | none => True
   | some v => ValueCompat v τ) ∧
  σ' = declareObjectStateWithNext σ τ x ov aNext

/--
Legacy façade for object declaration.

The operational policy may now choose a post-state cursor explicitly,
so the old relation is retained as an existential wrapper around the
new `DeclaresObjectWithNext` relation.
-/
def DeclaresObject (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (σ' : State) : Prop :=
  ∃ aNext, DeclaresObjectWithNext σ τ x ov aNext σ'

@[simp] theorem declaresObject_iff_exists_withNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {σ' : State} :
    DeclaresObject σ τ x ov σ' ↔
      ∃ aNext, DeclaresObjectWithNext σ τ x ov aNext σ' := by
  rfl

@[simp] theorem declaresObject_of_withNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {aNext : Nat} {σ' : State} :
    DeclaresObjectWithNext σ τ x ov aNext σ' →
      DeclaresObject σ τ x ov σ' := by
  intro h
  exact ⟨aNext, h⟩


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

end Cpp
