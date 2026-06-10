import CppFormalization.Cpp3.Boundary.All
import CppFormalization.Cpp3.Typing.Judgment.Surface

/-!
# CppFormalization.Cpp3.Soundness2.Source.Boundary

Source vocabulary for boundary realization, independent of the old `Soundness`
and old top-level `Realization` trees.

This file deliberately does not say that typing alone gives runtime readiness.
A boundary source keeps four kinds of lower evidence visible:

* typing/static entry information;
* effect surface;
* safe-fragment obligations;
* concrete runtime entry evidence for the current state.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Typed static source for a statement boundary. -/
structure TypedStmtStaticSource
    (Γ : TypeEnv) (st : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ
  static : Static.StaticStmtBoundaryInfo Γ st

namespace TypedStmtStaticSource

/-- Project the static boundary information carried by the typed source. -/
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

/-- Source for constructing a concrete statement runtime boundary. -/
structure StmtBoundarySource
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  typedStatic : TypedStmtStaticSource Γ st
  effect : Effects.StmtEffect Γ st
  safety : SafetyFragment.StmtSafetyFragment Γ st
  entry : Boundary.StmtEntryEvidence Γ σ st

namespace StmtBoundarySource

/-- Build the concrete statement boundary from its source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundarySource Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  Boundary.StmtBoundary.mk
    h.typedStatic.static
    h.effect
    h.safety
    h.entry

end StmtBoundarySource

/-- Source for constructing a concrete block-body runtime boundary. -/
structure BlockBoundarySource
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  typedStatic : TypedBlockStaticSource Γ body
  effect : Effects.BlockEffect Γ body
  safety : SafetyFragment.BlockSafetyFragment Γ body
  entry : Boundary.BlockEntryEvidence Γ σ body

namespace BlockBoundarySource

/-- Build the concrete block boundary from its source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundarySource Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  Boundary.BlockBoundary.mk
    h.typedStatic.static
    h.effect
    h.safety
    h.entry

end BlockBoundarySource

/-- Source for constructing a closed function-body runtime boundary. -/
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

/-- Build the concrete function-body boundary from its source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundarySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body where
  static := h.static
  effect := h.effect
  safety := h.safety
  entry := h.entry

end FunctionBodyBoundarySource

end Source
end Soundness2
end Cpp3
