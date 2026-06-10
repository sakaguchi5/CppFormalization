import CppFormalization.Cpp3.Boundary.All
import CppFormalization.Cpp3.Typing.Judgment.Surface

/-!
# CppFormalization.Cpp3.Soundness.Derive.BoundaryConstruction.Core

Bottom-up constructors for runtime entry boundaries.

Phase 4 starts the layer that builds `Boundary` objects from the pieces that are
mathematically and C++-semantically below them:

* a visible control-indexed typing judgment, recording why the program point is
  statically meaningful;
* static boundary information, which exposes the entry/control surface consumed
  by Boundary;
* effect and safe-fragment packages, which describe what the program may touch
  and which C++ safety obligations are in force;
* concrete runtime entry evidence for the current state.

The key point is negative as well as positive: typing alone does not produce a
runtime boundary, because runtime readiness depends on the concrete state.  This
file therefore keeps the typed source visible while constructing the Boundary
only after the effect, safety, and runtime-entry evidence have also been supplied.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace BoundaryConstruction

/-- Typed static source for a statement boundary.

C++ reading: `st` has a visible Cpp3 control-indexed typing judgment, and the
static entry surface required by the runtime boundary has been extracted or
constructed for the same statement. -/
structure TypedStmtStaticSource
    (Γ : TypeEnv) (st : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ
  static : Static.StaticStmtBoundaryInfo Γ st

namespace TypedStmtStaticSource

/-- Project the static statement boundary information carried by the typed source. -/
def boundaryInfo
    {Γ : TypeEnv} {st : CppStmt}
    (h : TypedStmtStaticSource Γ st) :
    Static.StaticStmtBoundaryInfo Γ st :=
  h.static

end TypedStmtStaticSource

/-- Typed static source for a block-body boundary. -/
structure TypedBlockStaticSource
    (Γ : TypeEnv) (body : StmtBlock) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ
  static : Static.StaticBlockBoundaryInfo Γ body

namespace TypedBlockStaticSource

/-- Project the static block boundary information carried by the typed source. -/
def boundaryInfo
    {Γ : TypeEnv} {body : StmtBlock}
    (h : TypedBlockStaticSource Γ body) :
    Static.StaticBlockBoundaryInfo Γ body :=
  h.static

end TypedBlockStaticSource

/-- Bottom-up source for a statement runtime boundary.

The `typedStatic` field records the typing-facing justification; the actual
runtime boundary is assembled only once the effect, safe-fragment, and concrete
entry evidence have also been supplied. -/
structure StmtBoundarySource
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  typedStatic : TypedStmtStaticSource Γ st
  effect : Effects.StmtEffect Γ st
  safety : SafetyFragment.StmtSafetyFragment Γ st
  entry : Boundary.StmtEntryEvidence Γ σ st

namespace StmtBoundarySource

/-- Build the concrete statement boundary from the bottom-up source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundarySource Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  Boundary.StmtBoundary.mk
    h.typedStatic.static
    h.effect
    h.safety
    h.entry

/-- Convenience constructor when the typed static source has already been built. -/
def mkBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (typedStatic : TypedStmtStaticSource Γ st)
    (effect : Effects.StmtEffect Γ st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  (StmtBoundarySource.mk typedStatic effect safety entry).toBoundary

end StmtBoundarySource

/-- Bottom-up source for a block-body runtime boundary. -/
structure BlockBoundarySource
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  typedStatic : TypedBlockStaticSource Γ body
  effect : Effects.BlockEffect Γ body
  safety : SafetyFragment.BlockSafetyFragment Γ body
  entry : Boundary.BlockEntryEvidence Γ σ body

namespace BlockBoundarySource

/-- Build the concrete block boundary from the bottom-up source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundarySource Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  Boundary.BlockBoundary.mk
    h.typedStatic.static
    h.effect
    h.safety
    h.entry

/-- Convenience constructor when the typed static source has already been built. -/
def mkBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (typedStatic : TypedBlockStaticSource Γ body)
    (effect : Effects.BlockEffect Γ body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  (BlockBoundarySource.mk typedStatic effect safety entry).toBoundary

end BlockBoundarySource

/-- Bottom-up source for a function-body boundary.

A function body boundary is the closed-body surface consumed by the final theorem:
static function-body control, function-body effects, safe-fragment obligations,
and an already constructed statement entry boundary for the body.  A visible
statement typing judgment is carried separately so this package records the
Typing contribution without pretending that typing alone gives runtime entry. -/
structure FunctionBodyBoundarySource
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ
  static : Static.StaticFunctionBodyBoundaryInfo Γ body
  effect : Effects.FunctionBodyEffect Γ body
  safety : SafetyFragment.FunctionBodySafetyFragment Γ body
  entry : Boundary.StmtBoundary Γ σ body

namespace FunctionBodyBoundarySource

/-- Build the concrete function-body boundary from the bottom-up source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundarySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body where
  static := h.static
  effect := h.effect
  safety := h.safety
  entry := h.entry

end FunctionBodyBoundarySource

namespace StmtEntryEvidence

/-- Entry evidence for `skip`. -/
def skip {Γ : TypeEnv} {σ : State} :
    Boundary.StmtEntryEvidence Γ σ .skip :=
  Boundary.StmtEntryEvidence.skip

/-- Entry evidence for an expression statement from its primitive expression boundary. -/
def exprStmt
    {Γ : TypeEnv} {σ : State} {es : CppExprStmt} {Readable : Prop}
    (boundary : Boundary.ExprStmtBoundary Γ σ es Readable) :
    Boundary.StmtEntryEvidence Γ σ (.exprStmt es) :=
  Boundary.StmtEntryEvidence.exprStmt boundary

/-- Entry evidence for an assignment from its primitive assignment boundary. -/
def assign
    {Γ : TypeEnv} {σ : State} {a : CppAssign} {Writable : Prop}
    (boundary : Boundary.AssignBoundary Γ σ a Writable) :
    Boundary.StmtEntryEvidence Γ σ (.assign a) :=
  Boundary.StmtEntryEvidence.assign boundary

/-- Entry evidence for a declaration from its primitive declaration boundary. -/
def decl
    {Γ Δ : TypeEnv} {σ : State} {d : CppDecl} {DeclarationSafe : Prop}
    (boundary : Boundary.DeclBoundary Γ Δ σ d DeclarationSafe) :
    Boundary.StmtEntryEvidence Γ σ (.decl d) :=
  Boundary.StmtEntryEvidence.decl boundary

/-- Entry evidence for a sequence from the already constructed head boundary. -/
def seqHead
    {Γ : TypeEnv} {σ : State} {head tail : CppStmt}
    (headBoundary : Boundary.StmtBoundary Γ σ head) :
    Boundary.StmtEntryEvidence Γ σ (.seq head tail) :=
  Boundary.StmtEntryEvidence.seqHead headBoundary

/-- Entry evidence for an if-statement from the condition boundary. -/
def iteCond
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond) :
    Boundary.StmtEntryEvidence Γ σ (.ite cond thenBranch elseBranch) :=
  Boundary.StmtEntryEvidence.iteCond condition

/-- Entry evidence for a while-statement from the condition boundary. -/
def whileCond
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (condition : Boundary.CondBoundary Γ Γc σ cond) :
    Boundary.StmtEntryEvidence Γ σ (.whileStmt cond body) :=
  Boundary.StmtEntryEvidence.whileCond condition

/-- Entry evidence for a block statement from the opened-body route and boundary. -/
def blockOpened
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body)
    (effect : Effects.OpenedBlockEffectSurface Γ Γopen body)
    (route : Semantics.OpenedBlockRoute σ σopened body)
    (bodyBoundary : Boundary.BlockBoundary Γopen σopened body) :
    Boundary.StmtEntryEvidence Γ σ (.block body) :=
  Boundary.StmtEntryEvidence.blockOpened static effect route bodyBoundary

/-- Entry evidence for a jump statement from its primitive jump boundary. -/
def jump
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.JumpBoundary Γ σ j) :
    Boundary.StmtEntryEvidence Γ σ (.jump j) :=
  Boundary.StmtEntryEvidence.jump boundary

end StmtEntryEvidence

namespace BlockEntryEvidence

/-- Entry evidence for an empty block body. -/
def nil {Γ : TypeEnv} {σ : State} :
    Boundary.BlockEntryEvidence Γ σ .nil :=
  Boundary.BlockEntryEvidence.nil

/-- Entry evidence for a nonempty block from the already constructed head boundary. -/
def consHead
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (headBoundary : Boundary.StmtBoundary Γ σ head) :
    Boundary.BlockEntryEvidence Γ σ (.cons head tail) :=
  Boundary.BlockEntryEvidence.consHead headBoundary

end BlockEntryEvidence

end BoundaryConstruction
end Derive
end Soundness
end Cpp3
