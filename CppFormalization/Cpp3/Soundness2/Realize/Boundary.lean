import CppFormalization.Cpp3.Soundness2.Source.Boundary

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Boundary

Realization theorem/def layer for boundary sources.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

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

/-- Build statement effect from static formation. -/
def stmtEffect_of_formed
    (Γ : TypeEnv) {st : CppStmt}
    (formed : Static.StaticStmtFormed st) :
    Effects.StmtEffect Γ st :=
  Effects.StmtEffect.ofStaticBoundary
    (staticStmtBoundaryInfo_of_formed Γ formed)

/-- Build block effect from static formation. -/
def blockEffect_of_formed
    (Γ : TypeEnv) {body : StmtBlock}
    (formed : Static.StaticBlockFormed body) :
    Effects.BlockEffect Γ body :=
  Effects.BlockEffect.ofStaticBoundary
    (staticBlockBoundaryInfo_of_formed Γ formed)

/-- Realize a typed/static statement source from typing and static information. -/
def typedStmtStaticSource_of_static
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (static : Static.StaticStmtBoundaryInfo Γ st) :
    Source.TypedStmtStaticSource Γ st where
  k := k
  Δ := Δ
  typed := typed
  static := static

/-- Realize a typed/static statement source from typing and static formation. -/
def typedStmtStaticSource_of_formed
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st) :
    Source.TypedStmtStaticSource Γ st :=
  typedStmtStaticSource_of_static typed
    (staticStmtBoundaryInfo_of_formed Γ formed)

/-- Realize a typed/static block source from typing and static information. -/
def typedBlockStaticSource_of_static
    {Γ : TypeEnv} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (static : Static.StaticBlockBoundaryInfo Γ body) :
    Source.TypedBlockStaticSource Γ body where
  k := k
  Δ := Δ
  typed := typed
  static := static

/-- Realize a typed/static block source from typing and static formation. -/
def typedBlockStaticSource_of_formed
    {Γ : TypeEnv} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body) :
    Source.TypedBlockStaticSource Γ body :=
  typedBlockStaticSource_of_static typed
    (staticBlockBoundaryInfo_of_formed Γ formed)

/-- Realize a statement boundary source from explicit lower components. -/
def stmtBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (typedStatic : Source.TypedStmtStaticSource Γ st)
    (effect : Effects.StmtEffect Γ st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Source.StmtBoundarySource Γ σ st where
  typedStatic := typedStatic
  effect := effect
  safety := safety
  entry := entry

/-- Realize a statement boundary source from typing, static formation, safety, and
runtime entry evidence. -/
def stmtBoundarySource_of_formed
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Source.StmtBoundarySource Γ σ st :=
  stmtBoundarySource_of_components
    (typedStmtStaticSource_of_formed typed formed)
    (stmtEffect_of_formed Γ formed)
    safety
    entry

/-- Realize a concrete statement boundary from lower components. -/
def stmtBoundary_of_formed
    {Γ : TypeEnv} {σ : State} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ st Δ)
    (formed : Static.StaticStmtFormed st)
    (safety : SafetyFragment.StmtSafetyFragment Γ st)
    (entry : Boundary.StmtEntryEvidence Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  (stmtBoundarySource_of_formed typed formed safety entry).toBoundary

/-- Realize a block boundary source from explicit lower components. -/
def blockBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (typedStatic : Source.TypedBlockStaticSource Γ body)
    (effect : Effects.BlockEffect Γ body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Source.BlockBoundarySource Γ σ body where
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
    Source.BlockBoundarySource Γ σ body :=
  blockBoundarySource_of_components
    (typedBlockStaticSource_of_formed typed formed)
    (blockEffect_of_formed Γ formed)
    safety
    entry

/-- Realize a concrete block boundary from lower components. -/
def blockBoundary_of_formed
    {Γ : TypeEnv} {σ : State} {body : StmtBlock} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeBlockCI k Γ body Δ)
    (formed : Static.StaticBlockFormed body)
    (safety : SafetyFragment.BlockSafetyFragment Γ body)
    (entry : Boundary.BlockEntryEvidence Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  (blockBoundarySource_of_formed typed formed safety entry).toBoundary

/-- Build a function-body effect from static function-body information and a
statement effect. -/
def functionBodyEffect_of_stmtEffect
    {Γ : TypeEnv} {body : CppStmt}
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (effect : Effects.StmtEffect Γ body) :
    Effects.FunctionBodyEffect Γ body where
  static := static
  effect := effect

/-- Build function-body safety from function-body effect and statement safety. -/
def functionBodySafety_of_stmtSafety
    {Γ : TypeEnv} {body : CppStmt}
    (effect : Effects.FunctionBodyEffect Γ body)
    (stmtSafety : SafetyFragment.StmtSafetyFragment Γ body) :
    SafetyFragment.FunctionBodySafetyFragment Γ body where
  effect := effect
  stmtSafety := stmtSafety

/-- Realize a function-body boundary source from explicit lower components. -/
def functionBodyBoundarySource_of_components
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (effect : Effects.FunctionBodyEffect Γ body)
    (safety : SafetyFragment.FunctionBodySafetyFragment Γ body)
    (entry : Boundary.StmtBoundary Γ σ body) :
    Source.FunctionBodyBoundarySource Γ σ body where
  k := k
  Δ := Δ
  typed := typed
  static := static
  effect := effect
  safety := safety
  entry := entry

/-- Realize a function-body boundary source from an already realized statement
boundary source plus the function-body static control surface. -/
def functionBodyBoundarySource_of_stmtSource
    {Γ : TypeEnv} {σ : State} {body : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (typed : Typing.Judgment.HasTypeStmtCI k Γ body Δ)
    (static : Static.StaticFunctionBodyBoundaryInfo Γ body)
    (stmtSource : Source.StmtBoundarySource Γ σ body) :
    Source.FunctionBodyBoundarySource Γ σ body :=
  let stmtBoundary := stmtSource.toBoundary
  let fbEffect := functionBodyEffect_of_stmtEffect static stmtSource.effect
  let fbSafety := functionBodySafety_of_stmtSafety fbEffect stmtSource.safety
  functionBodyBoundarySource_of_components typed static fbEffect fbSafety stmtBoundary

end Realize
end Soundness2
end Cpp3
