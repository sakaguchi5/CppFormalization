import CppFormalization.Cpp3.Soundness2.Realize.ClassificationCompound

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationConcrete

Concrete assembly layer for Step 5--8 of Soundness2 classification realization.

`ClassificationKernel` and `ClassificationCompound` fixed the full-syntax case
surface.  This file turns lower classifier theorem bundles into the primitive,
compound, block, and function-body case families, and then assembles the full
classification kernel/provider sources.

The layer is deliberately forward-moving:

* primitive statement cases are supplied by primitive progress/classification
  theorems;
* compound statement cases are supplied by lower compound classifiers, with the
  while-statement case derived directly from loop-behavior evidence;
* block cases are supplied by lower block classifiers;
* function-body cases are supplied separately because the function-body semantic
  target is not the same proposition as statement classification.

Thus this file fills the `StmtClassificationCases`, `BlockClassificationCases`,
and `FunctionBodyClassificationCases` families from lower theorem inputs without
claiming that `BoundarySource` alone is sufficient.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Step 5 lower theorem bundle for primitive statement classification. -/
structure PrimitiveStmtClassificationTheorems : Type where
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

namespace PrimitiveStmtClassificationTheorems

/-- Realize primitive statement classification cases from lower theorems. -/
def toCases
    (P : PrimitiveStmtClassificationTheorems) :
    PrimitiveStmtClassificationCases where
  skip := P.skip
  exprStmt := P.exprStmt
  assign := P.assign
  decl := P.decl
  jump := P.jump

end PrimitiveStmtClassificationTheorems

/-- A while-boundary source is classified by the loop-behavior certificate. -/
theorem closedWhileStmtSoundness_of_loopBehavior
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (source : Source.StmtBoundarySource Γ σ (.whileStmt cond body)) :
    Source.ClosedStmtSoundness σ (.whileStmt cond body) := by
  rcases loopBehavior.certify source.toBoundary with ⟨Γc, cert⟩
  exact cert.closedWhileSoundness

/-- Component-level variant of while statement classification. -/
theorem closedWhileStmtSoundness_of_componentLoopBehavior
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (source : Source.StmtBoundarySource Γ σ (.whileStmt cond body)) :
    Source.ClosedStmtSoundness σ (.whileStmt cond body) := by
  rcases loopBehavior source.toBoundary with ⟨Γc, component⟩
  exact component.toCertificate.closedWhileSoundness

/-- Step 6 lower theorem bundle for non-while compound statement classification.

The while case is intentionally not a field here: it is derived from
`LoopBehaviorCertificateTheorem` by
`closedWhileStmtSoundness_of_loopBehavior`. -/
structure CompoundStmtClassificationTheorems : Type where
  seq :
    ∀ {Γ : TypeEnv} {σ : State} {head tail : CppStmt},
      Source.StmtBoundarySource Γ σ (.seq head tail) →
        Source.ClosedStmtSoundness σ (.seq head tail)
  ite :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Source.StmtBoundarySource Γ σ (.ite cond thenBranch elseBranch) →
        Source.ClosedStmtSoundness σ (.ite cond thenBranch elseBranch)
  block :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.StmtBoundarySource Γ σ (.block body) →
        Source.ClosedStmtSoundness σ (.block body)

namespace CompoundStmtClassificationTheorems

/-- Realize compound statement cases, deriving while from loop behavior. -/
def toCases
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (P : CompoundStmtClassificationTheorems) :
    CompoundStmtClassificationCases where
  seq := P.seq
  ite := P.ite
  whileStmt := closedWhileStmtSoundness_of_loopBehavior loopBehavior
  block := P.block

/-- Component-level variant, deriving while from a lower loop-behavior certifier. -/
def toCasesWithComponentLoopBehavior
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    (P : CompoundStmtClassificationTheorems) :
    CompoundStmtClassificationCases where
  seq := P.seq
  ite := P.ite
  whileStmt := closedWhileStmtSoundness_of_componentLoopBehavior loopBehavior
  block := P.block

end CompoundStmtClassificationTheorems

/-- Step 5+6 theorem bundle for all statement classification cases. -/
structure StmtClassificationTheorems : Type where
  primitive : PrimitiveStmtClassificationTheorems
  compound : CompoundStmtClassificationTheorems

namespace StmtClassificationTheorems

/-- Realize the split statement case family from lower theorem bundles. -/
def toCaseFamily
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (P : StmtClassificationTheorems) :
    StmtClassificationCaseFamily where
  primitive := P.primitive.toCases
  compound := P.compound.toCases loopBehavior

/-- Realize the full statement case surface. -/
def toCases
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (P : StmtClassificationTheorems) :
    StmtClassificationCases :=
  (P.toCaseFamily loopBehavior).toCases

/-- Realize the statement classifier. -/
def toRealization
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (P : StmtClassificationTheorems) :
    StmtClassifierRealization :=
  (P.toCaseFamily loopBehavior).toRealization

/-- Component-level variant of the statement case family. -/
def toCaseFamilyWithComponentLoopBehavior
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    (P : StmtClassificationTheorems) :
    StmtClassificationCaseFamily where
  primitive := P.primitive.toCases
  compound := P.compound.toCasesWithComponentLoopBehavior loopBehavior

end StmtClassificationTheorems

/-- Step 7 lower theorem bundle for block classification. -/
structure BlockClassificationTheorems : Type where
  nil :
    ∀ {Γ : TypeEnv} {σ : State},
      Source.BlockBoundarySource Γ σ .nil →
        Source.ClosedBlockSoundness σ .nil
  cons :
    ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
      Source.BlockBoundarySource Γ σ (.cons head tail) →
        Source.ClosedBlockSoundness σ (.cons head tail)

namespace BlockClassificationTheorems

/-- Realize block classification cases from lower block theorems. -/
def toCases
    (P : BlockClassificationTheorems) :
    BlockCompoundClassificationCases where
  nil := P.nil
  cons := P.cons

/-- Realize the block classifier. -/
def toRealization
    (P : BlockClassificationTheorems) :
    BlockClassifierRealization :=
  P.toCases.toRealization

end BlockClassificationTheorems

/-- Step 8 lower theorem bundle for primitive function-body classification. -/
structure PrimitiveFunctionBodyClassificationTheorems : Type where
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

namespace PrimitiveFunctionBodyClassificationTheorems

/-- Realize primitive function-body cases from lower theorems. -/
def toCases
    (P : PrimitiveFunctionBodyClassificationTheorems) :
    PrimitiveFunctionBodyClassificationCases where
  skip := P.skip
  exprStmt := P.exprStmt
  assign := P.assign
  decl := P.decl
  jump := P.jump

end PrimitiveFunctionBodyClassificationTheorems

/-- Step 8 lower theorem bundle for compound function-body classification. -/
structure CompoundFunctionBodyClassificationTheorems : Type where
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

namespace CompoundFunctionBodyClassificationTheorems

/-- Realize compound function-body cases from lower theorems. -/
def toCases
    (P : CompoundFunctionBodyClassificationTheorems) :
    CompoundFunctionBodyClassificationCases where
  seq := P.seq
  ite := P.ite
  whileStmt := P.whileStmt
  block := P.block

end CompoundFunctionBodyClassificationTheorems

/-- Step 8 lower theorem bundle for all function-body classification cases. -/
structure FunctionBodyClassificationTheorems : Type where
  primitive : PrimitiveFunctionBodyClassificationTheorems
  compound : CompoundFunctionBodyClassificationTheorems

namespace FunctionBodyClassificationTheorems

/-- Realize the split function-body case family from lower theorem bundles. -/
def toCaseFamily
    (P : FunctionBodyClassificationTheorems) :
    FunctionBodyClassificationCaseFamily where
  primitive := P.primitive.toCases
  compound := P.compound.toCases

/-- Realize the full function-body case surface. -/
def toCases
    (P : FunctionBodyClassificationTheorems) :
    FunctionBodyClassificationCases :=
  P.toCaseFamily.toCases

/-- Realize the function-body classifier. -/
def toRealization
    (P : FunctionBodyClassificationTheorems) :
    FunctionBodyClassifierRealization :=
  P.toCaseFamily.toRealization

end FunctionBodyClassificationTheorems

/-- Step 5--8 theorem bundle for the whole closed-internal classification case
family. -/
structure ClassificationConcreteTheorems : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior : Source.LoopBehaviorCertificateTheorem
  stmt : StmtClassificationTheorems
  block : BlockClassificationTheorems
  functionBody : FunctionBodyClassificationTheorems

namespace ClassificationConcreteTheorems

/-- Realize the primitive/compound case family. -/
def toCaseFamily
    (P : ClassificationConcreteTheorems) :
    ClassificationCaseFamily where
  localControl := P.localControl
  scopeExit := P.scopeExit
  loopBehavior := P.loopBehavior
  stmt := P.stmt.toCaseFamily P.loopBehavior
  block := P.block.toCases
  functionBody := P.functionBody.toCaseFamily

/-- Realize the full classification kernel. -/
def toClassificationKernel
    (P : ClassificationConcreteTheorems) :
    ClassificationKernel :=
  P.toCaseFamily.toClassificationKernel

/-- Realize the named classification source bundle. -/
def toClassificationSources
    (P : ClassificationConcreteTheorems) :
    ClassificationRealizationSources :=
  P.toCaseFamily.toClassificationSources

/-- Realize final closed-internal provider sources. -/
def toProviderSources
    (P : ClassificationConcreteTheorems) :
    Source.ClosedInternalProviderSources :=
  P.toCaseFamily.toProviderSources

end ClassificationConcreteTheorems

/-- Component-level Step 5--8 theorem bundle. -/
structure ComponentClassificationConcreteTheorems : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorComponentSource Γ Γc σ cond body
  stmt : StmtClassificationTheorems
  block : BlockClassificationTheorems
  functionBody : FunctionBodyClassificationTheorems

namespace ComponentClassificationConcreteTheorems

/-- Realize the component-level primitive/compound case family. -/
def toCaseFamily
    (P : ComponentClassificationConcreteTheorems) :
    ComponentClassificationCaseFamily where
  localControl := P.localControl
  scopeExit := P.scopeExit
  loopBehavior := P.loopBehavior
  stmt := P.stmt.toCaseFamilyWithComponentLoopBehavior P.loopBehavior
  block := P.block.toCases
  functionBody := P.functionBody.toCaseFamily

/-- Realize the component-level classification kernel. -/
def toComponentClassificationKernel
    (P : ComponentClassificationConcreteTheorems) :
    ComponentClassificationKernel :=
  P.toCaseFamily.toComponentClassificationKernel

/-- Convert to the ordinary classification kernel. -/
def toClassificationKernel
    (P : ComponentClassificationConcreteTheorems) :
    ClassificationKernel :=
  P.toCaseFamily.toClassificationKernel

/-- Realize final closed-internal provider sources. -/
def toProviderSources
    (P : ComponentClassificationConcreteTheorems) :
    Source.ClosedInternalProviderSources :=
  P.toCaseFamily.toProviderSources

end ComponentClassificationConcreteTheorems

end Realize
end Soundness2
end Cpp3
