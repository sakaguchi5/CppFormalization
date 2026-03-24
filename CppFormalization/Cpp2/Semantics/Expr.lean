import CppFormalization.Cpp2.Core.RuntimeState
import CppFormalization.Cpp2.Core.Syntax

/-!
Concrete place/value evaluation.
-/

namespace Cpp

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


/-!
Safety layer built on top of concrete place/value evaluation.

`ValidPlace` means the place resolves to a live cell.
`ReadablePlace` strengthens this by requiring an initialized value.

`NoUninit*` now distinguishes addressability from readability:
- places used as places only need to be valid
- values read through `load` need readable places

`NoInvalidRef*` focuses only on ruling out dangling / dead references,
so it is phrased in terms of `ValidPlace`.
-/

end Cpp
