import CppFormalization.Cpp3.Soundness2.Realize.Boundary
import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Realize.BoundarySources

Stronger bottom-up boundary-source realizers.

`Realize.Boundary` already contains the primitive constructors.  This file adds
small lower-component packages so later proof layers can pass around one
mathematically meaningful object instead of repeatedly threading typing,
formation, safety, and runtime-entry evidence by hand.

The design is intentionally honest: safety fragments and runtime entry evidence
are still explicit inputs.  Typing/static formation can produce the static and
effect surfaces, but it does not by itself produce runtime readiness.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Lower components sufficient to realize a statement boundary source. -/
structure StmtBoundaryLowerComponents
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ
  formed : Static.StaticStmtFormed st
  safety : SafetyFragment.StmtSafetyFragment Γ st
  entry : Boundary.StmtEntryEvidence Γ σ st

namespace StmtBoundaryLowerComponents

/-- Realize the typed/static source. -/
def typedStatic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Source.TypedStmtStaticSource Γ st :=
  typedStmtStaticSource_of_formed h.typed h.formed

/-- Realize the static boundary information. -/
def staticInfo
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Static.StaticStmtBoundaryInfo Γ st :=
  staticStmtBoundaryInfo_of_formed Γ h.formed

/-- Realize the statement effect surface. -/
def effect
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Effects.StmtEffect Γ st :=
  stmtEffect_of_formed Γ h.formed

/-- Realize the statement boundary source. -/
def toBoundarySource
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Source.StmtBoundarySource Γ σ st :=
  stmtBoundarySource_of_formed h.typed h.formed h.safety h.entry

/-- Realize the concrete statement boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  h.toBoundarySource.toBoundary

/-- Realize the closed-internal statement source. -/
def toClosedInternalSource
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundaryLowerComponents Γ σ st) :
    Source.ClosedInternalStmtSource Γ σ st where
  boundarySource := h.toBoundarySource

end StmtBoundaryLowerComponents

/-- Lower components sufficient to realize a block boundary source. -/
structure BlockBoundaryLowerComponents
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ
  formed : Static.StaticBlockFormed body
  safety : SafetyFragment.BlockSafetyFragment Γ body
  entry : Boundary.BlockEntryEvidence Γ σ body

namespace BlockBoundaryLowerComponents

/-- Realize the typed/static block source. -/
def typedStatic
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Source.TypedBlockStaticSource Γ body :=
  typedBlockStaticSource_of_formed h.typed h.formed

/-- Realize the static block boundary information. -/
def staticInfo
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Static.StaticBlockBoundaryInfo Γ body :=
  staticBlockBoundaryInfo_of_formed Γ h.formed

/-- Realize the block effect surface. -/
def effect
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Effects.BlockEffect Γ body :=
  blockEffect_of_formed Γ h.formed

/-- Realize the block boundary source. -/
def toBoundarySource
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Source.BlockBoundarySource Γ σ body :=
  blockBoundarySource_of_formed h.typed h.formed h.safety h.entry

/-- Realize the concrete block boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  h.toBoundarySource.toBoundary

/-- Realize the closed-internal block source. -/
def toClosedInternalSource
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundaryLowerComponents Γ σ body) :
    Source.ClosedInternalBlockSource Γ σ body where
  boundarySource := h.toBoundarySource

end BlockBoundaryLowerComponents

/-- Lower components sufficient to realize a function-body boundary source from
statement-level lower components and a function-body static surface. -/
structure FunctionBodyBoundaryLowerComponents
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ
  formed : Static.StaticStmtFormed body
  stmtSafety : SafetyFragment.StmtSafetyFragment Γ body
  entry : Boundary.StmtEntryEvidence Γ σ body
  functionStatic : Static.StaticFunctionBodyBoundaryInfo Γ body

namespace FunctionBodyBoundaryLowerComponents

/-- The statement-level lower components of a function body. -/
def stmtComponents
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    StmtBoundaryLowerComponents Γ σ body where
  k := h.k
  Δ := h.Δ
  typed := h.typed
  formed := h.formed
  safety := h.stmtSafety
  entry := h.entry

/-- Realize the statement boundary source for the function body. -/
def stmtBoundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Source.StmtBoundarySource Γ σ body :=
  h.stmtComponents.toBoundarySource

/-- Realize the statement boundary for the function body. -/
def stmtBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Boundary.StmtBoundary Γ σ body :=
  h.stmtBoundarySource.toBoundary

/-- Realize the function-body effect surface. -/
def effect
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Effects.FunctionBodyEffect Γ body :=
  functionBodyEffect_of_stmtEffect h.functionStatic h.stmtBoundarySource.effect

/-- Realize the function-body safety fragment. -/
def safety
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    SafetyFragment.FunctionBodySafetyFragment Γ body :=
  functionBodySafety_of_stmtSafety h.effect h.stmtSafety

/-- Realize the function-body boundary source. -/
def toBoundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Source.FunctionBodyBoundarySource Γ σ body :=
  functionBodyBoundarySource_of_stmtSource h.typed h.functionStatic h.stmtBoundarySource

/-- Realize the concrete function-body boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  h.toBoundarySource.toBoundary

/-- Realize the closed-internal function-body source. -/
def toClosedInternalSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyBoundaryLowerComponents Γ σ body) :
    Source.ClosedInternalFunctionBodySource Γ σ body where
  boundarySource := h.toBoundarySource

end FunctionBodyBoundaryLowerComponents

/-- Function-body source from an already realized statement boundary source and a
function-body static surface.  This is useful when statement-boundary generation
has already been factored elsewhere. -/
structure FunctionBodyFromStmtBoundarySource
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  k : ControlKind
  Δ : TypeEnv
  typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ
  functionStatic : Static.StaticFunctionBodyBoundaryInfo Γ body
  stmtSource : Source.StmtBoundarySource Γ σ body

namespace FunctionBodyFromStmtBoundarySource

/-- Realize the function-body boundary source. -/
def toBoundarySource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyFromStmtBoundarySource Γ σ body) :
    Source.FunctionBodyBoundarySource Γ σ body :=
  functionBodyBoundarySource_of_stmtSource h.typed h.functionStatic h.stmtSource

/-- Realize the concrete function-body boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyFromStmtBoundarySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  h.toBoundarySource.toBoundary

/-- Realize the closed-internal function-body source. -/
def toClosedInternalSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyFromStmtBoundarySource Γ σ body) :
    Source.ClosedInternalFunctionBodySource Γ σ body where
  boundarySource := h.toBoundarySource

end FunctionBodyFromStmtBoundarySource

end Realize
end Soundness2
end Cpp3
