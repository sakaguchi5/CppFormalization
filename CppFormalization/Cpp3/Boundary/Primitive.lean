import CppFormalization.Cpp3.Boundary.Expr
import CppFormalization.Cpp3.Semantics.Kernel.Primitive

/-!
# CppFormalization.Cpp3.Boundary.Primitive

Runtime boundaries for primitive statement payloads.
-/

namespace Cpp3
namespace Boundary

/-- Boundary for executing an assignment. -/
structure AssignBoundary (Γ : TypeEnv) (σ : State) (a : CppAssign) : Type where
  effect : Effects.AssignEffect Γ a
  safety : SafetyFragment.AssignSafetyFragment Γ a
  post : State
  step : Semantics.BigStepAssign σ a post
  writable : Prop
  writableEvidence : Contracts.Requires writable

/-- Boundary for executing a declaration. -/
structure DeclBoundary
    (Γ Δ : TypeEnv) (σ : State) (d : CppDecl) : Type where
  effect : Effects.DeclEffect Γ Δ d
  safety : SafetyFragment.DeclSafetyFragment Γ Δ d
  post : State
  step : Semantics.BigStepDecl σ d post
  declarationSafe : Prop
  declarationEvidence : Contracts.Requires declarationSafe

/-- Boundary for executing an expression statement. -/
structure ExprStmtBoundary
    (Γ : TypeEnv) (σ : State) (es : CppExprStmt) : Type where
  effect : Effects.ExprStmtEffect Γ es
  post : State
  step : Semantics.BigStepExprStmt σ es post
  readable : Prop
  readableEvidence : Contracts.Requires readable

/-- Boundary for executing a return payload. -/
structure ReturnBoundary
    (Γ : TypeEnv) (σ : State) (r : CppReturn) : Type where
  effect : Effects.ReturnEffect Γ r
  result : Option Value
  returnSafe : Prop
  returnEvidence : Contracts.Requires returnSafe

/-- Boundary for executing a jump. -/
structure JumpBoundary
    (Γ : TypeEnv) (σ : State) (j : CppJump) : Type where
  effect : Effects.JumpEffect Γ j
  result : CtrlResult
  post : State
  step : Semantics.BigStepJump σ j result post

end Boundary
end Cpp3
