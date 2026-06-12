import CppFormalization.Cpp4.Core.Program
import CppFormalization.Cpp4.Resource.Capability

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Expr

Finite kernel semantics for value expressions, place expressions, and call
arguments.

The kernel is intentionally ControlPlan-centered above this file, but expression
semantics still belongs at the bottom because atoms, loop guards, switch
conditions, and calls all depend on value evaluation.
-/

namespace Cpp4

/-- Runtime context available to the finite kernel semantics. -/
structure KernelContext where
  functions : FunctionEnv

namespace KernelContext

/-- Runtime context induced by a whole program. -/
def ofProgram (P : Program) : KernelContext where
  functions := P.functions

end KernelContext

mutual

/-- Evaluate a place expression to an address. -/
inductive BigStepPlace (χ : KernelContext) : State → PlaceExpr → Address → State → Prop where
  | var {σ : State} {x : Ident} {b : Binding} :
      lookupBinding σ x = some b →
      BigStepPlace χ σ (.var x) (bindingAddress b) σ
  | deref {σ σ' : State} {e : ValExpr} {a : Address} :
      BigStepValue χ σ e (.ptr (.addr a)) σ' →
      BigStepPlace χ σ (.deref e) a σ'

/-- Evaluate a value expression to a runtime value. -/
inductive BigStepValue (χ : KernelContext) : State → ValExpr → Value → State → Prop where
  | litBool {σ : State} {b : Bool} :
      BigStepValue χ σ (.litBool b) (.bool b) σ
  | litInt {σ : State} {n : Int} :
      BigStepValue χ σ (.litInt n) (.int n) σ
  | nullPtr {σ : State} :
      BigStepValue χ σ .nullPtr (.ptr .null) σ
  | load {σ σp : State} {p : PlaceExpr} {a : Address} {c : Cell} {v : Value} :
      BigStepPlace χ σ p a σp →
      heapAt σp a = some c →
      c.value = some v →
      BigStepValue χ σ (.load p) v σp
  | addrOf {σ σp : State} {p : PlaceExpr} {a : Address} :
      BigStepPlace χ σ p a σp →
      BigStepValue χ σ (.addrOf p) (.ptr (.addr a)) σp
  | addInt {σ σ₁ σ₂ : State} {lhs rhs : ValExpr} {m n : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      BigStepValue χ σ₁ rhs (.int n) σ₂ →
      BigStepValue χ σ (.add lhs rhs) (.int (m + n)) σ₂
  | subInt {σ σ₁ σ₂ : State} {lhs rhs : ValExpr} {m n : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      BigStepValue χ σ₁ rhs (.int n) σ₂ →
      BigStepValue χ σ (.sub lhs rhs) (.int (m - n)) σ₂
  | mulInt {σ σ₁ σ₂ : State} {lhs rhs : ValExpr} {m n : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      BigStepValue χ σ₁ rhs (.int n) σ₂ →
      BigStepValue χ σ (.mul lhs rhs) (.int (m * n)) σ₂
  | eqValue {σ σ₁ σ₂ : State} {lhs rhs : ValExpr} {v₁ v₂ : Value} :
      BigStepValue χ σ lhs v₁ σ₁ →
      BigStepValue χ σ₁ rhs v₂ σ₂ →
      BigStepValue χ σ (.eq lhs rhs) (.bool (decide (v₁ = v₂))) σ₂
  | ltInt {σ σ₁ σ₂ : State} {lhs rhs : ValExpr} {m n : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      BigStepValue χ σ₁ rhs (.int n) σ₂ →
      BigStepValue χ σ (.lt lhs rhs) (.bool (decide (m < n))) σ₂
  | notBool {σ σ' : State} {e : ValExpr} {b : Bool} :
      BigStepValue χ σ e (.bool b) σ' →
      BigStepValue χ σ (.not e) (.bool (!b)) σ'
  | call {σ σ' : State} {f : FunctionName} {args : CallArgs} {v : Value} :
      BigStepCall χ σ f args v σ' →
      BigStepValue χ σ (.call f args) v σ'

/-- Evaluate a custom call-argument list left-to-right. -/
inductive BigStepCallArgs (χ : KernelContext) : State → CallArgs → List Value → State → Prop where
  | nil {σ : State} :
      BigStepCallArgs χ σ .nil [] σ
  | cons {σ σ₁ σ₂ : State} {e : ValExpr} {es : CallArgs} {v : Value} {vs : List Value} :
      BigStepValue χ σ e v σ₁ →
      BigStepCallArgs χ σ₁ es vs σ₂ →
      BigStepCallArgs χ σ (.cons e es) (v :: vs) σ₂

/-- Kernel hook for callable execution.

Argument evaluation is fixed by the kernel.  The post-call state is deliberately
left relational so later internal/external-call layers can refine side effects
without changing expression semantics. -/
inductive BigStepCall (χ : KernelContext) : State → FunctionName → CallArgs → Value → State → Prop where
  | external {σ σargs σ' : State} {f : FunctionName} {args : CallArgs}
      {decl : CallableDecl} {values : List Value} {v : Value} :
      χ.functions.lookup f = some decl →
      decl.kind = .external →
      BigStepCallArgs χ σ args values σargs →
      ValueCompat v decl.sig.ret →
      BigStepCall χ σ f args v σ'
  | internalOpaque {σ σargs σ' : State} {f : FunctionName} {args : CallArgs}
      {decl : CallableDecl} {values : List Value} {v : Value} :
      χ.functions.lookup f = some decl →
      decl.kind = .internal →
      BigStepCallArgs χ σ args values σargs →
      ValueCompat v decl.sig.ret →
      BigStepCall χ σ f args v σ'

end

namespace BigStepValue

/-- A condition evaluates to the chosen Boolean value. -/
def CondValue (χ : KernelContext) (σ : State) (c : CppCond) (b : Bool) (σ' : State) : Prop :=
  match c with
  | .expr e => BigStepValue χ σ e (.bool b) σ'

/-- A switch condition evaluates to the chosen integer value. -/
def SwitchCondValue (χ : KernelContext) (σ : State) (c : CppSwitchCond) (n : Int) (σ' : State) : Prop :=
  match c with
  | .expr e => BigStepValue χ σ e (.int n) σ'

end BigStepValue

end Cpp4
