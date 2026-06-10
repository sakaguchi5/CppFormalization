import CppFormalization.Cpp3.Soundness.Derive.BoundaryConstruction.Core

/-!
# CppFormalization.Cpp3.Realization.BoundarySource

Realization layer for Phase 4 boundary sources.

`Soundness.Derive.BoundaryConstruction` defined the source objects consumed by the
closed-internal soundness assembly.  This file builds those source objects from
lower Cpp3 components: typing/static formation, effects, safety fragments, and
runtime entry evidence.

The point is deliberately not to claim that typing alone gives runtime readiness.
Runtime entry evidence and safety fragments remain explicit inputs.
-/

namespace Cpp3
namespace Realization
namespace BoundarySource

/-- Build static statement boundary information from static formation. -/
def staticStmtBoundaryInfo_of_formed
    (Γ : TypeEnv) {st : CppStmt}
    (formed : Static.StaticStmtFormed st) :
    Static.StaticStmtBoundaryInfo Γ st where
  entry := Static.StmtEntryWitness.canonical Γ formed

/-- Build static block boundary information from static formation. -/
def staticBlockBoundaryInfo_of_formed
    (Γ : TypeEnv) {body : StmtBlock}
    (formed : Static.StaticBlockFormed body) :
    Static.StaticBlockBoundaryInfo Γ body where
  entry := Static.BlockEntryWitness.canonical Γ formed

/-- Build a statement effect surface from static formation through the canonical
static statement boundary. -/
def stmtEffect_of_formed
    (Γ : TypeEnv) {st : CppStmt}
    (formed : Static.StaticStmtFormed st) :
    Effects.StmtEffect Γ st :=
  Effects.StmtEffect.ofStaticBoundary
    (staticStmtBoundaryInfo_of_formed Γ formed)

/-- Build a block effect surface from static formation through the canonical
static block boundary. -/
def blockEffect_of_formed
    (Γ : TypeEnv) {body : StmtBlock}
    (formed : Static.StaticBlockFormed body) :
    Effects.BlockEffect Γ body :=
  Effects.BlockEffect.ofStaticBoundary
    (staticBlockBoundaryInfo_of_formed Γ formed)

/-- Build the typed/static statement source used by the Soundness boundary
construction layer. -/
def typedStmtStaticSource_of_static
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (static : Static.StaticStmtBoundaryInfo Γ st) :
    Soundness.Derive.BoundaryConstruction.TypedStmtStaticSource Γ st where
  k := k
  Δ := Δ
  typed := typed
  static := static

/-- Build the typed/static statement source from typing plus static formation. -/
def typedStmtStaticSource_of_formed
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st) :
    Soundness.Derive.BoundaryConstruction.TypedStmtStaticSource Γ st :=
  typedStmtStaticSource_of_static typed
    (staticStmtBoundaryInfo_of_formed Γ formed)

/-- Build the typed/static block source used by the Soundness boundary
construction layer. -/
def typedBlockStaticSource_of_static
    {Γ : TypeEnv} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (static : Static.StaticBlockBoundaryInfo Γ body) :
    Soundness.Derive.BoundaryConstruction.TypedBlockStaticSource Γ body where
  k := k
  Δ := Δ
  typed := typed
  static := static

/-- Build the typed/static block source from typing plus static formation. -/
def typedBlockStaticSource_of_formed
    {Γ : TypeEnv} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body) :
    Soundness.Derive.BoundaryConstruction.TypedBlockStaticSource Γ body :=
  typedBlockStaticSource_of_static typed
    (staticBlockBoundaryInfo_of_formed Γ formed)

/-- Realize a statement boundary source from its explicit lower components. -/
def stmtBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (typedStatic : Soundness.Derive.BoundaryConstruction.TypedStmtStaticSource Γ st)
    (effect : Effects.StmtEffect Γ st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ st where
  typedStatic := typedStatic
  effect := effect
  safety := safety
  entry := entry

/-- Realize a statement boundary source from typing, static formation, safety, and
runtime entry evidence.  The effect surface is the canonical one induced by the
static boundary. -/
def stmtBoundarySource_of_formed
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ st :=
  stmtBoundarySource_of_components
    (typedStmtStaticSource_of_formed typed formed)
    (stmtEffect_of_formed Γ formed)
    safety
    entry

/-- Realize a concrete statement boundary directly from the lower components. -/
def stmtBoundary_of_formed
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  (stmtBoundarySource_of_formed typed formed safety entry).toBoundary

/-- Realize a block boundary source from its explicit lower components. -/
def blockBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (typedStatic : Soundness.Derive.BoundaryConstruction.TypedBlockStaticSource Γ body)
    (effect : Effects.BlockEffect Γ body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Soundness.Derive.BoundaryConstruction.BlockBoundarySource Γ σ body where
  typedStatic := typedStatic
  effect := effect
  safety := safety
  entry := entry

/-- Realize a block boundary source from typing, static formation, safety, and
runtime entry evidence. -/
def blockBoundarySource_of_formed
    {Γ : TypeEnv} {σ : State} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Soundness.Derive.BoundaryConstruction.BlockBoundarySource Γ σ body :=
  blockBoundarySource_of_components
    (typedBlockStaticSource_of_formed typed formed)
    (blockEffect_of_formed Γ formed)
    safety
    entry

/-- Realize a concrete block boundary directly from the lower components. -/
def blockBoundary_of_formed
    {Γ : TypeEnv} {σ : State} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  (blockBoundarySource_of_formed typed formed safety entry).toBoundary

/-- Build the function-body effect surface from the static function-body boundary
and the already realized statement effect. -/
def functionBodyEffect_of_stmtEffect
    {Γ : TypeEnv} {body : CppStmt}
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (effect : Effects.StmtEffect Γ body) :
    Effects.FunctionBodyEffect Γ body where
  static := static
  effect := effect

/-- Build a function-body safety fragment from a function-body effect and the
underlying statement safety fragment. -/
def functionBodySafety_of_stmtSafety
    {Γ : TypeEnv} {body : CppStmt}
    (effect : Effects.FunctionBodyEffect Γ body)
    (stmtSafety : SafetyFragment.StmtSafetyFragment Γ body) :
    SafetyFragment.FunctionBodySafetyFragment Γ body where
  effect := effect
  stmtSafety := stmtSafety

/-- Realize a function-body boundary source from its explicit lower components. -/
def functionBodyBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (effect : Effects.FunctionBodyEffect Γ body)
    (safety : SafetyFragment.FunctionBodySafetyFragment Γ body)
    (entry : Boundary.StmtBoundary Γ σ body) :
    Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body where
  k := k
  Δ := Δ
  typed := typed
  static := static
  effect := effect
  safety := safety
  entry := entry

/-- Realize a function-body boundary source from statement-level boundary pieces
plus the function-body static control surface. -/
def functionBodyBoundarySource_of_stmtSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (stmtSource : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ body) :
    Soundness.Derive.BoundaryConstruction.FunctionBodyBoundarySource Γ σ body :=
  let stmtBoundary := stmtSource.toBoundary
  let fbEffect := functionBodyEffect_of_stmtEffect static stmtSource.effect
  let fbSafety := functionBodySafety_of_stmtSafety fbEffect stmtSource.safety
  functionBodyBoundarySource_of_components typed static fbEffect fbSafety stmtBoundary

/-- Realize a concrete function-body boundary from statement-level source pieces. -/
def functionBodyBoundary_of_stmtSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (stmtSource : Soundness.Derive.BoundaryConstruction.StmtBoundarySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  (functionBodyBoundarySource_of_stmtSource typed static stmtSource).toBoundary

end BoundarySource
end Realization
end Cpp3
