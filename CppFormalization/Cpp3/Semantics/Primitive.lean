import CppFormalization.Cpp3.Semantics.Value

/-!
# CppFormalization.Cpp3.Semantics.Primitive

Primitive statement payload semantics: assignment, declaration, expression
statement, and jump payloads.

This layer names the operational effects themselves.  It does not state that the
program is well-typed, safe, stable, or contract-satisfying.
-/

namespace Cpp3
namespace Semantics

/-- Operational semantics of simple assignment. -/
inductive BigStepAssign : State → CppAssign → State → Prop where
  | simple
      {σ σ₁ : State} {p : PlaceExpr} {e : ValExpr}
      {τ : CppType} {a : Nat} {c : Cell} {v : Value} :
      BigStepPlace σ p τ a →
      BigStepValue σ e τ v →
      σ.heap a = some c →
      c.alive = true →
      c.ty = τ →
      σ₁ = writeHeap σ a { c with value := some v } →
      BigStepAssign σ (.simple p e) σ₁

/-- Operational semantics of declaration payloads. -/
inductive BigStepDecl : State → CppDecl → State → Prop where
  | objectNoInit
      {σ : State} {τ : CppType} {x : Ident} {aNext : Nat} :
      ObjectType τ →
      currentScopeFresh σ x →
      σ.heap σ.next = none →
      FreshPostCursor (declareObjectStateCore σ τ x none) aNext →
      BigStepDecl σ (.object τ x .noInit)
        (declareObjectStateWithNext σ τ x none aNext)

  | objectValue
      {σ : State} {τ : CppType} {x : Ident} {e : ValExpr} {v : Value}
      {aNext : Nat} :
      ObjectType τ →
      currentScopeFresh σ x →
      σ.heap σ.next = none →
      BigStepValue σ e τ v →
      ValueCompat v τ →
      FreshPostCursor (declareObjectStateCore σ τ x (some v)) aNext →
      BigStepDecl σ (.object τ x (.value e))
        (declareObjectStateWithNext σ τ x (some v) aNext)

  | ref
      {σ : State} {τ : CppType} {x : Ident} {p : PlaceExpr} {a : Nat} :
      currentScopeFresh σ x →
      BigStepPlace σ p τ a →
      BigStepDecl σ (.ref τ x p) (declareRefState σ τ x a)

/-- Operational semantics of expression statements. -/
inductive BigStepExprStmt : State → CppExprStmt → State → Prop where
  | discard
      {σ : State} {e : ValExpr} {τ : CppType} {v : Value} :
      BigStepValue σ e τ v →
      BigStepExprStmt σ (.discard e) σ

/-- Operational semantics of jump payloads. -/
inductive BigStepJump : State → CppJump → CtrlResult → State → Prop where
  | breakStmt
      {σ : State} :
      BigStepJump σ .breakStmt .breakResult σ

  | continueStmt
      {σ : State} :
      BigStepJump σ .continueStmt .continueResult σ

  | returnVoid
      {σ : State} :
      BigStepJump σ (.returnStmt .void) (.returnResult none) σ

  | returnValue
      {σ : State} {e : ValExpr} {τ : CppType} {v : Value} :
      BigStepValue σ e τ v →
      BigStepJump σ (.returnStmt (.value e)) (.returnResult (some v)) σ

end Semantics
end Cpp3
