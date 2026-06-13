import CppFormalization.Cpp4.Semantics.Kernel.Expr

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Expr

Divergence vocabulary for expression, place, call-argument, and callable
execution.  The first layer is rule-shaped and mirrors left-to-right evaluation.
-/

namespace Cpp4

mutual

/-- A place expression diverges while being evaluated to an address. -/
inductive DivergesPlace (χ : KernelContext) : State → PlaceExpr → Prop where
  | derefValue {σ : State} {e : ValExpr} :
      DivergesValue χ σ e →
      DivergesPlace χ σ (.deref e)

/-- A value expression diverges while being evaluated. -/
inductive DivergesValue (χ : KernelContext) : State → ValExpr → Prop where
  | loadPlace {σ : State} {p : PlaceExpr} :
      DivergesPlace χ σ p →
      DivergesValue χ σ (.load p)
  | addrOfPlace {σ : State} {p : PlaceExpr} :
      DivergesPlace χ σ p →
      DivergesValue χ σ (.addrOf p)
  | addLeft {σ : State} {lhs rhs : ValExpr} :
      DivergesValue χ σ lhs →
      DivergesValue χ σ (.add lhs rhs)
  | addRight {σ σ₁ : State} {lhs rhs : ValExpr} {m : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      DivergesValue χ σ₁ rhs →
      DivergesValue χ σ (.add lhs rhs)
  | subLeft {σ : State} {lhs rhs : ValExpr} :
      DivergesValue χ σ lhs →
      DivergesValue χ σ (.sub lhs rhs)
  | subRight {σ σ₁ : State} {lhs rhs : ValExpr} {m : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      DivergesValue χ σ₁ rhs →
      DivergesValue χ σ (.sub lhs rhs)
  | mulLeft {σ : State} {lhs rhs : ValExpr} :
      DivergesValue χ σ lhs →
      DivergesValue χ σ (.mul lhs rhs)
  | mulRight {σ σ₁ : State} {lhs rhs : ValExpr} {m : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      DivergesValue χ σ₁ rhs →
      DivergesValue χ σ (.mul lhs rhs)
  | eqLeft {σ : State} {lhs rhs : ValExpr} :
      DivergesValue χ σ lhs →
      DivergesValue χ σ (.eq lhs rhs)
  | eqRight {σ σ₁ : State} {lhs rhs : ValExpr} {v : Value} :
      BigStepValue χ σ lhs v σ₁ →
      DivergesValue χ σ₁ rhs →
      DivergesValue χ σ (.eq lhs rhs)
  | ltLeft {σ : State} {lhs rhs : ValExpr} :
      DivergesValue χ σ lhs →
      DivergesValue χ σ (.lt lhs rhs)
  | ltRight {σ σ₁ : State} {lhs rhs : ValExpr} {m : Int} :
      BigStepValue χ σ lhs (.int m) σ₁ →
      DivergesValue χ σ₁ rhs →
      DivergesValue χ σ (.lt lhs rhs)
  | notArg {σ : State} {e : ValExpr} :
      DivergesValue χ σ e →
      DivergesValue χ σ (.not e)
  | call {σ : State} {f : FunctionName} {args : CallArgs} :
      DivergesCall χ σ f args →
      DivergesValue χ σ (.call f args)

/-- A call-argument list diverges while being evaluated left-to-right. -/
inductive DivergesCallArgs (χ : KernelContext) : State → CallArgs → Prop where
  | head {σ : State} {e : ValExpr} {es : CallArgs} :
      DivergesValue χ σ e →
      DivergesCallArgs χ σ (.cons e es)
  | tail {σ σ₁ : State} {e : ValExpr} {es : CallArgs} {v : Value} :
      BigStepValue χ σ e v σ₁ →
      DivergesCallArgs χ σ₁ es →
      DivergesCallArgs χ σ (.cons e es)

/-- A callable execution diverges.  Argument evaluation is fixed by the kernel;
function-body/external divergence refinements can add more call-specific rules. -/
inductive DivergesCall (χ : KernelContext) : State → FunctionName → CallArgs → Prop where
  | args {σ : State} {f : FunctionName} {args : CallArgs} :
      DivergesCallArgs χ σ args →
      DivergesCall χ σ f args

end

namespace DivergesValue

/-- Divergence while evaluating a boolean condition. -/
def Cond (χ : KernelContext) (σ : State) (c : CppCond) : Prop :=
  match c with
  | .expr e => DivergesValue χ σ e

/-- Divergence while evaluating an integer switch condition. -/
def SwitchCond (χ : KernelContext) (σ : State) (c : CppSwitchCond) : Prop :=
  match c with
  | .expr e => DivergesValue χ σ e

end DivergesValue

end Cpp4
