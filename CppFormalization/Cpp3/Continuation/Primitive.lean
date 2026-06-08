import CppFormalization.Cpp3.Continuation.Core

/-!
# CppFormalization.Cpp3.Continuation.Primitive

Continuation-facing surfaces for primitive statement payloads.

Primitive execution produces a post-state, but it does not itself decide which
compound continuation consumes that post-state.  These packages pair the
syntax-directed statement entry boundary with the primitive stability package.
-/

namespace Cpp3
namespace Continuation

/-- Assignment statement continuation surface. -/
structure AssignStmtContinuation
    (Γ : TypeEnv) (σ σ₁ : State) (a : CppAssign) (Writable : Prop) : Type where
  source : Boundary.StmtBoundary Γ σ (.assign a)
  primitive : Stability.AssignBoundaryStability Γ σ σ₁ a Writable

namespace AssignStmtContinuation

/-- The post-state produced by the assignment payload. -/
def postState
    {Γ : TypeEnv} {σ σ₁ : State} {a : CppAssign} {Writable : Prop}
    (_ : AssignStmtContinuation Γ σ σ₁ a Writable) : State :=
  σ₁

end AssignStmtContinuation

/-- Declaration statement continuation surface. -/
structure DeclStmtContinuation
    (Γ Δ : TypeEnv) (σ σ₁ : State) (d : CppDecl)
    (DeclarationSafe : Prop) : Type where
  source : Boundary.StmtBoundary Γ σ (.decl d)
  primitive : Stability.DeclBoundaryStability Γ Δ σ σ₁ d DeclarationSafe

namespace DeclStmtContinuation

/-- The post-state produced by the declaration payload. -/
def postState
    {Γ Δ : TypeEnv} {σ σ₁ : State} {d : CppDecl} {DeclarationSafe : Prop}
    (_ : DeclStmtContinuation Γ Δ σ σ₁ d DeclarationSafe) : State :=
  σ₁

end DeclStmtContinuation

/-- Expression-statement continuation surface. -/
structure ExprStmtContinuation
    (Γ : TypeEnv) (σ σ₁ : State) (es : CppExprStmt) (Readable : Prop) : Type where
  source : Boundary.StmtBoundary Γ σ (.exprStmt es)
  primitive : Stability.ExprStmtBoundaryStability Γ σ σ₁ es Readable

namespace ExprStmtContinuation

/-- The post-state produced by the expression statement payload. -/
def postState
    {Γ : TypeEnv} {σ σ₁ : State} {es : CppExprStmt} {Readable : Prop}
    (_ : ExprStmtContinuation Γ σ σ₁ es Readable) : State :=
  σ₁

end ExprStmtContinuation

/-- Jump statement continuation surface. -/
structure JumpStmtContinuation
    (Γ : TypeEnv) (σ σ₁ : State) (j : CppJump) (r : CtrlResult) : Type where
  source : Boundary.StmtBoundary Γ σ (.jump j)
  primitive : Stability.JumpBoundaryStability Γ σ σ₁ j r

namespace JumpStmtContinuation

/-- The post-state produced by the jump payload. -/
def postState
    {Γ : TypeEnv} {σ σ₁ : State} {j : CppJump} {r : CtrlResult}
    (_ : JumpStmtContinuation Γ σ σ₁ j r) : State :=
  σ₁

/-- The control result produced by the jump payload. -/
def result
    {Γ : TypeEnv} {σ σ₁ : State} {j : CppJump} {r : CtrlResult}
    (_ : JumpStmtContinuation Γ σ σ₁ j r) : CtrlResult :=
  r

end JumpStmtContinuation

/-- Return-payload continuation surface before it is wrapped as a jump. -/
structure ReturnPayloadContinuation
    (Γ : TypeEnv) (σ : State) (ret : CppReturn) (ReturnSafe : Prop) : Type where
  primitive : Stability.ReturnBoundaryStability Γ σ ret ReturnSafe

end Continuation
end Cpp3
