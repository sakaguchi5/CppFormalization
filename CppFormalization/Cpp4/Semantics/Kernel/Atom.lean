import CppFormalization.Cpp4.Semantics.Kernel.Call
import CppFormalization.Cpp4.Resource.Effect.Core

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Atom

Finite kernel semantics for primitive statement atoms.
-/

namespace Cpp4

namespace KernelState

/-- Address chosen by the first allocation policy. -/
def nextAddress (σ : State) : Address :=
  { object := { id := σ.nextObject } }

/-- Scope id chosen by the first scope-opening policy. -/
def nextScopeId (σ : State) : ScopeId :=
  { id := σ.nextScope }

/-- Allocate a fresh object in the current top scope and bind its name there. -/
def allocObject (σ : State) (x : Ident) (τ : CppType) (ov : Option Value) : State :=
  match σ.scopes with
  | [] => σ
  | fr :: rest =>
      let oid : ObjectId := { id := σ.nextObject }
      let a : Address := { object := oid }
      let cell : Cell := {
        ty := τ
        value := ov
        lifetime := { owner := fr.id, status := .live }
      }
      { σ with
        scopes := { fr with
          binds := fun y => if y = x then some (.object τ a) else fr.binds y
          locals := oid :: fr.locals
        } :: rest
        heap := fun q => if q = oid then some cell else σ.heap q
        nextObject := σ.nextObject + 1 }

/-- Bind a reference name in the current top scope. -/
def bindRef (σ : State) (x : Ident) (τ : CppType) (a : Address) : State :=
  match σ.scopes with
  | [] => σ
  | fr :: rest =>
      { σ with
        scopes := { fr with
          binds := fun y => if y = x then some (.ref τ a) else fr.binds y
        } :: rest }

/-- Open a fresh runtime scope according to the first kernel policy. -/
def openScope (σ : State) : State :=
  { pushScopeState σ (nextScopeId σ) with nextScope := σ.nextScope + 1 }

end KernelState

/-- Evaluate an initializer payload. -/
inductive BigStepInit (χ : KernelContext) : State → CppInit → Option Value → State → Prop where
  | noInit {σ : State} :
      BigStepInit χ σ .noInit none σ
  | value {σ σ' : State} {e : ValExpr} {v : Value} :
      BigStepValue χ σ e v σ' →
      BigStepInit χ σ (.value e) (some v) σ'

/-- Execute a declaration. -/
inductive BigStepDecl (χ : KernelContext) : State → CppDecl → State → Prop where
  | object {σ σinit : State} {τ : CppType} {x : Ident} {init : CppInit} {ov : Option Value} :
      BigStepInit χ σ init ov σinit →
      BigStepDecl χ σ (.object τ x init) (KernelState.allocObject σinit x τ ov)
  | ref {σ σp : State} {τ : CppType} {x : Ident} {p : PlaceExpr} {a : Address} :
      BigStepPlace χ σ p a σp →
      BigStepDecl χ σ (.ref τ x p) (KernelState.bindRef σp x τ a)

/-- Execute an expression statement. -/
inductive BigStepExprStmt (χ : KernelContext) : State → CppExprStmt → State → Prop where
  | discard {σ σ' : State} {e : ValExpr} {v : Value} :
      BigStepValue χ σ e v σ' →
      BigStepExprStmt χ σ (.discard e) σ'

/-- Execute a simple assignment. -/
inductive BigStepAssign (χ : KernelContext) : State → CppAssign → State → Prop where
  | simple {σ σp σv : State} {p : PlaceExpr} {e : ValExpr}
      {a : Address} {v : Value} {c : Cell} :
      BigStepPlace χ σ p a σp →
      BigStepValue χ σp e v σv →
      heapAt σv a = some c →
      BigStepAssign χ σ (.simple p e) (writeObjectState σv a c.ty v)

/-- Execute a restricted `for` initializer. -/
inductive BigStepForInit (χ : KernelContext) : State → CppForInit → State → Prop where
  | none {σ : State} :
      BigStepForInit χ σ .none σ
  | expr {σ σ' : State} {s : CppExprStmt} :
      BigStepExprStmt χ σ s σ' →
      BigStepForInit χ σ (.expr s) σ'
  | decl {σ σ' : State} {d : CppDecl} :
      BigStepDecl χ σ d σ' →
      BigStepForInit χ σ (.decl d) σ'

/-- Execute a restricted `for` iteration fragment. -/
inductive BigStepForIter (χ : KernelContext) : State → CppForIter → State → Prop where
  | none {σ : State} :
      BigStepForIter χ σ .none σ
  | expr {σ σ' : State} {s : CppExprStmt} :
      BigStepExprStmt χ σ s σ' →
      BigStepForIter χ σ (.expr s) σ'
  | assign {σ σ' : State} {a : CppAssign} :
      BigStepAssign χ σ a σ' →
      BigStepForIter χ σ (.assign a) σ'

/-- Execute a primitive ControlPlan atom. -/
inductive BigStepAtom (χ : KernelContext) : State → ControlAtom → CtrlResult → State → Prop where
  | skip {σ : State} :
      BigStepAtom χ σ .skip .normal σ
  | exprStmt {σ σ' : State} {s : CppExprStmt} :
      BigStepExprStmt χ σ s σ' →
      BigStepAtom χ σ (.exprStmt s) .normal σ'
  | assign {σ σ' : State} {a : CppAssign} :
      BigStepAssign χ σ a σ' →
      BigStepAtom χ σ (.assign a) .normal σ'
  | decl {σ σ' : State} {d : CppDecl} :
      BigStepDecl χ σ d σ' →
      BigStepAtom χ σ (.decl d) .normal σ'
  | jumpBreak {σ : State} :
      BigStepAtom χ σ (.jump .breakStmt) .breakResult σ
  | jumpCont {σ : State} :
      BigStepAtom χ σ (.jump .continueStmt) .continueResult σ
  | returnVoid {σ : State} :
      BigStepAtom χ σ (.jump (.returnStmt .void)) .returnVoid σ
  | returnValue {σ σ' : State} {e : ValExpr} {v : Value} :
      BigStepValue χ σ e v σ' →
      BigStepAtom χ σ (.jump (.returnStmt (.value e))) (.returnValue v) σ'

end Cpp4
