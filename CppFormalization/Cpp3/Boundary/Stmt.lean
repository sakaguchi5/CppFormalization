import CppFormalization.Cpp3.Boundary.Primitive
import CppFormalization.Cpp3.Semantics.Kernel.Stmt
import CppFormalization.Cpp3.Semantics.SelectedRoute.Basic

/-!
# CppFormalization.Cpp3.Boundary.Stmt

Runtime entry boundaries for statements, block bodies, and function bodies.

A statement/block boundary is now split into a common surface
(static/effect/safety) plus syntax-directed runtime entry evidence.  It still does
not say that the statement terminates, diverges, or preserves later boundaries.
Post-state continuation boundaries remain in `Boundary.Flow`, and preservation of
those boundaries remains in `Stability`.
-/

namespace Cpp3
namespace Boundary

mutual

/-- Runtime boundary for entering a statement in a concrete state. -/
inductive StmtBoundary : TypeEnv → State → CppStmt → Type where
  | mk
      {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (static : Static.StaticStmtBoundaryInfo Γ st)
      (effect : Effects.StmtEffect Γ st)
      (safety : SafetyFragment.StmtSafetyFragment Γ st)
      (entry : StmtEntryEvidence Γ σ st) :
      StmtBoundary Γ σ st

/-- Runtime boundary for entering a block body in a concrete state. -/
inductive BlockBoundary : TypeEnv → State → StmtBlock → Type where
  | mk
      {Γ : TypeEnv} {σ : State} {body : StmtBlock}
      (static : Static.StaticBlockBoundaryInfo Γ body)
      (effect : Effects.BlockEffect Γ body)
      (safety : SafetyFragment.BlockSafetyFragment Γ body)
      (entry : BlockEntryEvidence Γ σ body) :
      BlockBoundary Γ σ body

/-- Syntax-directed evidence explaining where statement execution can start.

For compound statements this evidence intentionally records only the first runtime
entry point.  Tail/branch/backedge/opened-body continuation facts live in
`Boundary.Flow`, `Stability`, and `Continuation`. -/
inductive StmtEntryEvidence : TypeEnv → State → CppStmt → Type where
  | skip
      {Γ : TypeEnv} {σ : State} :
      StmtEntryEvidence Γ σ .skip

  | exprStmt
      {Γ : TypeEnv} {σ : State} {es : CppExprStmt} {Readable : Prop}
      (boundary : ExprStmtBoundary Γ σ es Readable) :
      StmtEntryEvidence Γ σ (.exprStmt es)

  | assign
      {Γ : TypeEnv} {σ : State} {a : CppAssign} {Writable : Prop}
      (boundary : AssignBoundary Γ σ a Writable) :
      StmtEntryEvidence Γ σ (.assign a)

  | decl
      {Γ Δ : TypeEnv} {σ : State} {d : CppDecl} {DeclarationSafe : Prop}
      (boundary : DeclBoundary Γ Δ σ d DeclarationSafe) :
      StmtEntryEvidence Γ σ (.decl d)

  | seqHead
      {Γ : TypeEnv} {σ : State} {head tail : CppStmt}
      (headBoundary : StmtBoundary Γ σ head) :
      StmtEntryEvidence Γ σ (.seq head tail)

  | iteCond
      {Γ Γc : TypeEnv} {σ : State} {cond : CppCond}
      {thenBranch elseBranch : CppStmt}
      (condition : CondBoundary Γ Γc σ cond) :
      StmtEntryEvidence Γ σ (.ite cond thenBranch elseBranch)

  | whileCond
      {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
      (condition : CondBoundary Γ Γc σ cond) :
      StmtEntryEvidence Γ σ (.whileStmt cond body)

  | blockOpened
      {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
      (static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body)
      (effect : Effects.OpenedBlockEffectSurface Γ Γopen body)
      (route : Semantics.OpenedBlockRoute σ σopened body)
      (bodyBoundary : BlockBoundary Γopen σopened body) :
      StmtEntryEvidence Γ σ (.block body)

  | jump
      {Γ : TypeEnv} {σ : State} {j : CppJump}
      (boundary : JumpBoundary Γ σ j) :
      StmtEntryEvidence Γ σ (.jump j)

/-- Syntax-directed evidence explaining where block-body execution can start. -/
inductive BlockEntryEvidence : TypeEnv → State → StmtBlock → Type where
  | nil
      {Γ : TypeEnv} {σ : State} :
      BlockEntryEvidence Γ σ .nil

  | consHead
      {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
      (headBoundary : StmtBoundary Γ σ head) :
      BlockEntryEvidence Γ σ (.cons head tail)

end

namespace StmtBoundary

/-- Project the static statement boundary surface. -/
def static
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : Static.StaticStmtBoundaryInfo Γ st :=
  match h with
  | .mk static _ _ _ => static

/-- Project the statement effect surface. -/
def effect
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : Effects.StmtEffect Γ st :=
  match h with
  | .mk _ effect _ _ => effect

/-- Project the statement safe-fragment surface. -/
def safety
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : SafetyFragment.StmtSafetyFragment Γ st :=
  match h with
  | .mk _ _ safety _ => safety

/-- Project the syntax-directed runtime entry evidence. -/
def entry
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : StmtEntryEvidence Γ σ st :=
  match h with
  | .mk _ _ _ entry => entry

/-- Alias for projecting statement entry evidence. -/
def get
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : StmtEntryEvidence Γ σ st :=
  h.entry

end StmtBoundary

namespace BlockBoundary

/-- Project the static block boundary surface. -/
def static
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : Static.StaticBlockBoundaryInfo Γ body :=
  match h with
  | .mk static _ _ _ => static

/-- Project the block effect surface. -/
def effect
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : Effects.BlockEffect Γ body :=
  match h with
  | .mk _ effect _ _ => effect

/-- Project the block safe-fragment surface. -/
def safety
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : SafetyFragment.BlockSafetyFragment Γ body :=
  match h with
  | .mk _ _ safety _ => safety

/-- Project the syntax-directed runtime entry evidence. -/
def entry
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : BlockEntryEvidence Γ σ body :=
  match h with
  | .mk _ _ _ entry => entry

/-- Alias for projecting block entry evidence. -/
def get
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : BlockEntryEvidence Γ σ body :=
  h.entry

end BlockBoundary

/-- Runtime boundary for a function body. -/
structure FunctionBodyBoundary
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  static : Static.StaticFunctionBodyBoundaryInfo Γ body
  effect : Effects.FunctionBodyEffect Γ body
  safety : SafetyFragment.FunctionBodySafetyFragment Γ body
  entry : StmtBoundary Γ σ body

end Boundary
end Cpp3
