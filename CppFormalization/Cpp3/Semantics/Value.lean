import CppFormalization.Cpp3.Core.All

/-!
# CppFormalization.Cpp3.Semantics.Value

Thin value/place/condition evaluation kernel.

This file deliberately contains only operational evaluation relations.  It does
not import Typing, Static, Boundary, Contracts, Stability, or Continuation.
Those later layers explain when the evaluations are safe and stable; this layer
only records what the C++ core fragment does when the relevant runtime facts are
available.
-/

namespace Cpp3
namespace Semantics

mutual

/-- Runtime evaluation of a place expression to an address and the place type. -/
inductive BigStepPlace : State → PlaceExpr → CppType → Nat → Prop where
  | varObject
      {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
      lookupBinding σ x = some (.object τ a) →
      BigStepPlace σ (.var x) τ a

  | varRef
      {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
      lookupBinding σ x = some (.ref τ a) →
      BigStepPlace σ (.var x) τ a

  | deref
      {σ : State} {e : ValExpr} {τ : CppType} {a : Nat} :
      BigStepValue σ e (.ptr τ) (.addr a) →
      BigStepPlace σ (.deref e) τ a

/-- Runtime evaluation of a value expression to a typed value. -/
inductive BigStepValue : State → ValExpr → CppType → Value → Prop where
  | litBool
      {σ : State} {b : Bool} :
      BigStepValue σ (.litBool b) (.base .bool) (.bool b)

  | litInt
      {σ : State} {n : Int} :
      BigStepValue σ (.litInt n) (.base .int) (.int n)

  | load
      {σ : State} {p : PlaceExpr} {τ : CppType} {a : Nat}
      {c : Cell} {v : Value} :
      BigStepPlace σ p τ a →
      σ.heap a = some c →
      c.alive = true →
      c.ty = τ →
      c.value = some v →
      ValueCompat v τ →
      BigStepValue σ (.load p) τ v

  | addrOf
      {σ : State} {p : PlaceExpr} {τ : CppType} {a : Nat} :
      BigStepPlace σ p τ a →
      BigStepValue σ (.addrOf p) (.ptr τ) (.addr a)

  | add
      {σ : State} {e₁ e₂ : ValExpr} {n₁ n₂ : Int} :
      BigStepValue σ e₁ (.base .int) (.int n₁) →
      BigStepValue σ e₂ (.base .int) (.int n₂) →
      BigStepValue σ (.add e₁ e₂) (.base .int) (.int (n₁ + n₂))

  | sub
      {σ : State} {e₁ e₂ : ValExpr} {n₁ n₂ : Int} :
      BigStepValue σ e₁ (.base .int) (.int n₁) →
      BigStepValue σ e₂ (.base .int) (.int n₂) →
      BigStepValue σ (.sub e₁ e₂) (.base .int) (.int (n₁ - n₂))

  | mul
      {σ : State} {e₁ e₂ : ValExpr} {n₁ n₂ : Int} :
      BigStepValue σ e₁ (.base .int) (.int n₁) →
      BigStepValue σ e₂ (.base .int) (.int n₂) →
      BigStepValue σ (.mul e₁ e₂) (.base .int) (.int (n₁ * n₂))

  | eqBool
      {σ : State} {e₁ e₂ : ValExpr} {b₁ b₂ : Bool} :
      BigStepValue σ e₁ (.base .bool) (.bool b₁) →
      BigStepValue σ e₂ (.base .bool) (.bool b₂) →
      BigStepValue σ (.eq e₁ e₂) (.base .bool) (.bool (decide (b₁ = b₂)))

  | eqInt
      {σ : State} {e₁ e₂ : ValExpr} {n₁ n₂ : Int} :
      BigStepValue σ e₁ (.base .int) (.int n₁) →
      BigStepValue σ e₂ (.base .int) (.int n₂) →
      BigStepValue σ (.eq e₁ e₂) (.base .bool) (.bool (decide (n₁ = n₂)))

  | eqAddr
      {σ : State} {e₁ e₂ : ValExpr} {τ : CppType} {a₁ a₂ : Nat} :
      BigStepValue σ e₁ (.ptr τ) (.addr a₁) →
      BigStepValue σ e₂ (.ptr τ) (.addr a₂) →
      BigStepValue σ (.eq e₁ e₂) (.base .bool) (.bool (decide (a₁ = a₂)))

  | lt
      {σ : State} {e₁ e₂ : ValExpr} {n₁ n₂ : Int} :
      BigStepValue σ e₁ (.base .int) (.int n₁) →
      BigStepValue σ e₂ (.base .int) (.int n₂) →
      BigStepValue σ (.lt e₁ e₂) (.base .bool) (.bool (decide (n₁ < n₂)))

  | not
      {σ : State} {e : ValExpr} {b : Bool} :
      BigStepValue σ e (.base .bool) (.bool b) →
      BigStepValue σ (.not e) (.base .bool) (.bool (!b))

end

/-- Runtime evaluation of a control condition.

The current syntax has expression-only conditions, so the post-state is the same
state.  The relation is nevertheless state-to-state so later side-effecting
conditions can be inserted without changing the branch/loop route vocabulary.
-/
inductive BigStepCond : State → CppCond → Bool → State → Prop where
  | expr
      {σ : State} {e : ValExpr} {b : Bool} :
      BigStepValue σ e (.base .bool) (.bool b) →
      BigStepCond σ (.expr e) b σ

end Semantics
end Cpp3
