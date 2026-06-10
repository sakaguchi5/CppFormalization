import CppFormalization.Cpp3.Soundness2.Realize.ClassificationKernel

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationCompound

Primitive/compound assembly for full-syntax Soundness2 classification cases.

`ClassificationKernel` fixed the full case surface.  This file refines that
surface by separating the statement and function-body cases into primitive and
compound groups, then assembling the complete `StmtClassificationCases`,
`BlockClassificationCases`, `FunctionBodyClassificationCases`, and finally the
full `ClassificationKernel`.

This is intentionally still a theorem-surface layer: the primitive and compound
case fields are the places where later files plug in concrete lower proofs from
primitive progress, local-control, scope-exit, and loop-behavior evidence.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Primitive statement classification cases.

These are the statement constructors that do not choose a statement/block
continuation by executing a sub-statement. -/
structure PrimitiveStmtClassificationCases : Type where
  skip :
    ∀ {Γ : TypeEnv} {σ : State},
      Source.StmtBoundarySource Γ σ .skip →
        Source.ClosedStmtSoundness σ .skip
  exprStmt :
    ∀ {Γ : TypeEnv} {σ : State} {e : CppExprStmt},
      Source.StmtBoundarySource Γ σ (.exprStmt e) →
        Source.ClosedStmtSoundness σ (.exprStmt e)
  assign :
    ∀ {Γ : TypeEnv} {σ : State} {a : CppAssign},
      Source.StmtBoundarySource Γ σ (.assign a) →
        Source.ClosedStmtSoundness σ (.assign a)
  decl :
    ∀ {Γ : TypeEnv} {σ : State} {d : CppDecl},
      Source.StmtBoundarySource Γ σ (.decl d) →
        Source.ClosedStmtSoundness σ (.decl d)
  jump :
    ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
      Source.StmtBoundarySource Γ σ (.jump j) →
        Source.ClosedStmtSoundness σ (.jump j)

/-- Compound statement classification cases.

These are the statement constructors whose classification depends on selected
routes, local-control handoffs, scope-exit, loop behavior, or recursive
statement/block classification. -/
structure CompoundStmtClassificationCases : Type where
  seq :
    ∀ {Γ : TypeEnv} {σ : State} {head tail : CppStmt},
      Source.StmtBoundarySource Γ σ (.seq head tail) →
        Source.ClosedStmtSoundness σ (.seq head tail)
  ite :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Source.StmtBoundarySource Γ σ (.ite cond thenBranch elseBranch) →
        Source.ClosedStmtSoundness σ (.ite cond thenBranch elseBranch)
  whileStmt :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Source.StmtBoundarySource Γ σ (.whileStmt cond body) →
        Source.ClosedStmtSoundness σ (.whileStmt cond body)
  block :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.StmtBoundarySource Γ σ (.block body) →
        Source.ClosedStmtSoundness σ (.block body)

namespace StmtClassificationCases

/-- Assemble all statement cases from primitive and compound case families. -/
def ofPrimitiveCompound
    (primitive : PrimitiveStmtClassificationCases)
    (compound : CompoundStmtClassificationCases) :
    StmtClassificationCases where
  skip := primitive.skip
  exprStmt := primitive.exprStmt
  assign := primitive.assign
  decl := primitive.decl
  seq := compound.seq
  ite := compound.ite
  whileStmt := compound.whileStmt
  block := compound.block
  jump := primitive.jump

end StmtClassificationCases

/-- Complete statement case family split into primitive and compound pieces. -/
structure StmtClassificationCaseFamily : Type where
  primitive : PrimitiveStmtClassificationCases
  compound : CompoundStmtClassificationCases

namespace StmtClassificationCaseFamily

/-- Assemble the full statement case surface. -/
def toCases
    (K : StmtClassificationCaseFamily) :
    StmtClassificationCases :=
  StmtClassificationCases.ofPrimitiveCompound K.primitive K.compound

/-- Assemble the statement classifier realization. -/
def toRealization
    (K : StmtClassificationCaseFamily) :
    StmtClassifierRealization :=
  K.toCases.toRealization

end StmtClassificationCaseFamily

/-- Block classification cases.

Block bodies have only two current constructors.  `nil` is the empty block body;
`cons` is the compound block-tail handoff case. -/
structure BlockCompoundClassificationCases : Type where
  nil :
    ∀ {Γ : TypeEnv} {σ : State},
      Source.BlockBoundarySource Γ σ .nil →
        Source.ClosedBlockSoundness σ .nil
  cons :
    ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
      Source.BlockBoundarySource Γ σ (.cons head tail) →
        Source.ClosedBlockSoundness σ (.cons head tail)

namespace BlockCompoundClassificationCases

/-- Assemble the full block case surface. -/
def toCases
    (K : BlockCompoundClassificationCases) :
    BlockClassificationCases where
  nil := K.nil
  cons := K.cons

/-- Assemble the block classifier realization. -/
def toRealization
    (K : BlockCompoundClassificationCases) :
    BlockClassifierRealization :=
  K.toCases.toRealization

end BlockCompoundClassificationCases

/-- Primitive function-body classification cases.

This is separate from primitive statement classification because the semantic
function-body target is not the same proposition as statement classification,
especially around return and other abrupt control. -/
structure PrimitiveFunctionBodyClassificationCases : Type where
  skip :
    ∀ {Γ : TypeEnv} {σ : State},
      Source.FunctionBodyBoundarySource Γ σ .skip →
        Source.ClosedFunctionBodySoundness σ .skip
  exprStmt :
    ∀ {Γ : TypeEnv} {σ : State} {e : CppExprStmt},
      Source.FunctionBodyBoundarySource Γ σ (.exprStmt e) →
        Source.ClosedFunctionBodySoundness σ (.exprStmt e)
  assign :
    ∀ {Γ : TypeEnv} {σ : State} {a : CppAssign},
      Source.FunctionBodyBoundarySource Γ σ (.assign a) →
        Source.ClosedFunctionBodySoundness σ (.assign a)
  decl :
    ∀ {Γ : TypeEnv} {σ : State} {d : CppDecl},
      Source.FunctionBodyBoundarySource Γ σ (.decl d) →
        Source.ClosedFunctionBodySoundness σ (.decl d)
  jump :
    ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
      Source.FunctionBodyBoundarySource Γ σ (.jump j) →
        Source.ClosedFunctionBodySoundness σ (.jump j)

/-- Compound function-body classification cases. -/
structure CompoundFunctionBodyClassificationCases : Type where
  seq :
    ∀ {Γ : TypeEnv} {σ : State} {head tail : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ (.seq head tail) →
        Source.ClosedFunctionBodySoundness σ (.seq head tail)
  ite :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ (.ite cond thenBranch elseBranch) →
        Source.ClosedFunctionBodySoundness σ (.ite cond thenBranch elseBranch)
  whileStmt :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ (.whileStmt cond body) →
        Source.ClosedFunctionBodySoundness σ (.whileStmt cond body)
  block :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.FunctionBodyBoundarySource Γ σ (.block body) →
        Source.ClosedFunctionBodySoundness σ (.block body)

namespace FunctionBodyClassificationCases

/-- Assemble all function-body cases from primitive and compound case families. -/
def ofPrimitiveCompound
    (primitive : PrimitiveFunctionBodyClassificationCases)
    (compound : CompoundFunctionBodyClassificationCases) :
    FunctionBodyClassificationCases where
  skip := primitive.skip
  exprStmt := primitive.exprStmt
  assign := primitive.assign
  decl := primitive.decl
  seq := compound.seq
  ite := compound.ite
  whileStmt := compound.whileStmt
  block := compound.block
  jump := primitive.jump

end FunctionBodyClassificationCases

/-- Complete function-body case family split into primitive and compound pieces. -/
structure FunctionBodyClassificationCaseFamily : Type where
  primitive : PrimitiveFunctionBodyClassificationCases
  compound : CompoundFunctionBodyClassificationCases

namespace FunctionBodyClassificationCaseFamily

/-- Assemble the full function-body case surface. -/
def toCases
    (K : FunctionBodyClassificationCaseFamily) :
    FunctionBodyClassificationCases :=
  FunctionBodyClassificationCases.ofPrimitiveCompound K.primitive K.compound

/-- Assemble the function-body classifier realization. -/
def toRealization
    (K : FunctionBodyClassificationCaseFamily) :
    FunctionBodyClassifierRealization :=
  K.toCases.toRealization

end FunctionBodyClassificationCaseFamily

/-- Primitive/compound split for the full classification kernel. -/
structure ClassificationCaseFamily : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior : Source.LoopBehaviorCertificateTheorem
  stmt : StmtClassificationCaseFamily
  block : BlockCompoundClassificationCases
  functionBody : FunctionBodyClassificationCaseFamily

namespace ClassificationCaseFamily

/-- Assemble the full-syntax classification kernel. -/
def toClassificationKernel
    (K : ClassificationCaseFamily) :
    ClassificationKernel where
  localControl := K.localControl
  scopeExit := K.scopeExit
  loopBehavior := K.loopBehavior
  stmt := K.stmt.toCases
  block := K.block.toCases
  functionBody := K.functionBody.toCases

/-- Assemble the statement classifier realization. -/
def stmtRealization
    (K : ClassificationCaseFamily) :
    StmtClassifierRealization :=
  K.stmt.toRealization

/-- Assemble the block classifier realization. -/
def blockRealization
    (K : ClassificationCaseFamily) :
    BlockClassifierRealization :=
  K.block.toRealization

/-- Assemble the function-body classifier realization. -/
def functionBodyRealization
    (K : ClassificationCaseFamily) :
    FunctionBodyClassifierRealization :=
  K.functionBody.toRealization

/-- Assemble the classification-realization theorem bundle. -/
def toClassificationRealizationTheorems
    (K : ClassificationCaseFamily) :
    ClassificationRealizationTheorems :=
  K.toClassificationKernel.toClassificationRealizationTheorems

/-- Assemble the named classification source theorem bundle. -/
def toClassificationSources
    (K : ClassificationCaseFamily) :
    ClassificationRealizationSources :=
  K.toClassificationKernel.toClassificationSources

/-- Assemble final closed-internal provider sources. -/
def toProviderSources
    (K : ClassificationCaseFamily) :
    Source.ClosedInternalProviderSources :=
  K.toClassificationKernel.toProviderSources

end ClassificationCaseFamily

/-- Primitive/compound split for the component-level classification kernel, where
while behavior is supplied by the lower component certifier. -/
structure ComponentClassificationCaseFamily : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorComponentSource Γ Γc σ cond body
  stmt : StmtClassificationCaseFamily
  block : BlockCompoundClassificationCases
  functionBody : FunctionBodyClassificationCaseFamily

namespace ComponentClassificationCaseFamily

/-- Assemble the component-level full-syntax classification kernel. -/
def toComponentClassificationKernel
    (K : ComponentClassificationCaseFamily) :
    ComponentClassificationKernel where
  localControl := K.localControl
  scopeExit := K.scopeExit
  loopBehavior := K.loopBehavior
  stmt := K.stmt.toCases
  block := K.block.toCases
  functionBody := K.functionBody.toCases

/-- Convert to the ordinary classification kernel. -/
def toClassificationKernel
    (K : ComponentClassificationCaseFamily) :
    ClassificationKernel :=
  K.toComponentClassificationKernel.toClassificationKernel

/-- Assemble final closed-internal provider sources. -/
def toProviderSources
    (K : ComponentClassificationCaseFamily) :
    Source.ClosedInternalProviderSources :=
  K.toComponentClassificationKernel.toProviderSources

end ComponentClassificationCaseFamily

end Realize
end Soundness2
end Cpp3
