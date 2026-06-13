import CppFormalization.Cpp4.Semantics.Divergence.Expr

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Call

Call-facing divergence helpers.
-/

namespace Cpp4

namespace DivergesCall

/-- A call diverges before entering the callee when argument evaluation diverges. -/
def InArguments (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs) : Prop :=
  DivergesCallArgs χ σ args ∧ DivergesCall χ σ f args

end DivergesCall

end Cpp4
