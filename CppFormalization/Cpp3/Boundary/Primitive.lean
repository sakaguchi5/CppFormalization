import CppFormalization.Cpp3.Boundary.Expr
import CppFormalization.Cpp3.Semantics.Kernel.Primitive

/-!
# CppFormalization.Cpp3.Boundary.Primitive

Runtime boundaries for primitive statement payloads.

The primitive semantic step is concrete, while the corresponding safety premise is
kept visible at the type level.  This prevents a boundary from hiding which C++
runtime condition justified the primitive operation.
-/

namespace Cpp3
namespace Boundary

/-- Boundary for executing an assignment.

`Writable` is the visible runtime write-safety proposition used to justify the
assignment target. -/
structure AssignBoundary
    (Γ : TypeEnv) (σ : State) (a : CppAssign) (Writable : Prop) : Type where
  effect : Effects.AssignEffect Γ a
  safety : SafetyFragment.AssignSafetyFragment Γ a
  post : State
  step : Semantics.BigStepAssign σ a post
  writableEvidence : RuntimeBoundaryEvidence .writableTargetAvailable Writable

namespace AssignBoundary

/-- Extract the visible write-safety evidence carried by an assignment boundary. -/
def writable
    {Γ : TypeEnv} {σ : State} {a : CppAssign} {Writable : Prop}
    (h : AssignBoundary Γ σ a Writable) : Writable :=
  h.writableEvidence.get

end AssignBoundary

/-- Boundary for executing a declaration.

`DeclarationSafe` is the visible proposition explaining why the declaration is
safe for the surrounding runtime boundary. -/
structure DeclBoundary
    (Γ Δ : TypeEnv) (σ : State) (d : CppDecl) (DeclarationSafe : Prop) : Type where
  effect : Effects.DeclEffect Γ Δ d
  safety : SafetyFragment.DeclSafetyFragment Γ Δ d
  post : State
  step : Semantics.BigStepDecl σ d post
  declarationEvidence : RuntimeBoundaryEvidence .declarationDoesNotInvalidateLaterUse DeclarationSafe

namespace DeclBoundary

/-- Extract the visible declaration-safety evidence carried by a declaration boundary. -/
def declarationSafe
    {Γ Δ : TypeEnv} {σ : State} {d : CppDecl} {DeclarationSafe : Prop}
    (h : DeclBoundary Γ Δ σ d DeclarationSafe) : DeclarationSafe :=
  h.declarationEvidence.get

end DeclBoundary

/-- Boundary for executing an expression statement.

`Readable` is the visible proposition explaining why the expression-statement
reads are safe in the current runtime state. -/
structure ExprStmtBoundary
    (Γ : TypeEnv) (σ : State) (es : CppExprStmt) (Readable : Prop) : Type where
  effect : Effects.ExprStmtEffect Γ es
  post : State
  step : Semantics.BigStepExprStmt σ es post
  readableEvidence : RuntimeBoundaryEvidence .readableTargetAvailable Readable

namespace ExprStmtBoundary

/-- Extract the visible read-safety evidence carried by an expression-statement boundary. -/
def readable
    {Γ : TypeEnv} {σ : State} {es : CppExprStmt} {Readable : Prop}
    (h : ExprStmtBoundary Γ σ es Readable) : Readable :=
  h.readableEvidence.get

end ExprStmtBoundary

/-- Boundary for executing a return payload.

`ReturnSafe` is the visible proposition explaining why the return payload, if any,
can be read safely. -/
structure ReturnBoundary
    (Γ : TypeEnv) (σ : State) (r : CppReturn) (ReturnSafe : Prop) : Type where
  effect : Effects.ReturnEffect Γ r
  result : Option Value
  returnEvidence : RuntimeBoundaryEvidence .readableTargetAvailable ReturnSafe

namespace ReturnBoundary

/-- Extract the visible return-payload safety evidence carried by a return boundary. -/
def returnSafe
    {Γ : TypeEnv} {σ : State} {r : CppReturn} {ReturnSafe : Prop}
    (h : ReturnBoundary Γ σ r ReturnSafe) : ReturnSafe :=
  h.returnEvidence.get

end ReturnBoundary

/-- Boundary for executing a jump. -/
structure JumpBoundary
    (Γ : TypeEnv) (σ : State) (j : CppJump) : Type where
  effect : Effects.JumpEffect Γ j
  result : CtrlResult
  post : State
  step : Semantics.BigStepJump σ j result post

end Boundary
end Cpp3
