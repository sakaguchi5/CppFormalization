import CppFormalization.Cpp3.Soundness2.Realize.Classification

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationKernel

Full-syntax classification-kernel surface for Soundness2.

This file is intentionally a kernel surface, not a magical proof that
`BoundarySource` alone classifies every program.  It names one classifier theorem
for every current statement and block constructor, then assembles those case
classifiers into the `StmtClassifierRealization`, `BlockClassifierRealization`,
`FunctionBodyClassifierRealization`, and final classification/provider sources.

The intended next step is to replace each case field by concrete lower proofs
from primitive progress, local-control, scope-exit, and loop-behavior evidence.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Statement classifier cases, one field for every current `CppStmt`
constructor.

The compound cases are deliberately explicit.  `seq`/`block` are where
local-control and scope-exit are expected to enter; `whileStmt` is where the
loop-behavior certificate is expected to enter. -/
structure StmtClassificationCases : Type where
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
  jump :
    ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
      Source.StmtBoundarySource Γ σ (.jump j) →
        Source.ClosedStmtSoundness σ (.jump j)

namespace StmtClassificationCases

/-- Dispatch a statement boundary source to the constructor-specific classifier. -/
def classify
    (K : StmtClassificationCases)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.StmtBoundarySource Γ σ st) :
    Source.ClosedStmtSoundness σ st :=
  match st with
  | .skip => K.skip source
  | .exprStmt _e => K.exprStmt source
  | .assign _a => K.assign source
  | .decl _d => K.decl source
  | .seq _head _tail => K.seq source
  | .ite _cond _thenBranch _elseBranch => K.ite source
  | .whileStmt _cond _body => K.whileStmt source
  | .block _body => K.block source
  | .jump _j => K.jump source

/-- Turn statement cases into the existing classifier-realization object. -/
def toRealization
    (K : StmtClassificationCases) :
    StmtClassifierRealization where
  classify := K.classify

end StmtClassificationCases

/-- Block classifier cases, one field for every current `StmtBlock` constructor. -/
structure BlockClassificationCases : Type where
  nil :
    ∀ {Γ : TypeEnv} {σ : State},
      Source.BlockBoundarySource Γ σ .nil →
        Source.ClosedBlockSoundness σ .nil
  cons :
    ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
      Source.BlockBoundarySource Γ σ (.cons head tail) →
        Source.ClosedBlockSoundness σ (.cons head tail)

namespace BlockClassificationCases

/-- Dispatch a block boundary source to the constructor-specific classifier. -/
def classify
    (K : BlockClassificationCases)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.BlockBoundarySource Γ σ body) :
    Source.ClosedBlockSoundness σ body :=
  match body with
  | .nil => K.nil source
  | .cons _head _tail => K.cons source

/-- Turn block cases into the existing classifier-realization object. -/
def toRealization
    (K : BlockClassificationCases) :
    BlockClassifierRealization where
  classify := K.classify

end BlockClassificationCases

/-- Function-body classifier cases, one field for every current `CppStmt`
constructor when the statement is used as a closed function body.

This is intentionally separated from `StmtClassificationCases`: function bodies
have their own semantic target, especially around return handling. -/
structure FunctionBodyClassificationCases : Type where
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
  jump :
    ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
      Source.FunctionBodyBoundarySource Γ σ (.jump j) →
        Source.ClosedFunctionBodySoundness σ (.jump j)

namespace FunctionBodyClassificationCases

/-- Dispatch a function-body boundary source to the constructor-specific
classifier. -/
def classify
    (K : FunctionBodyClassificationCases)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body :=
  match body with
  | .skip => K.skip source
  | .exprStmt _e => K.exprStmt source
  | .assign _a => K.assign source
  | .decl _d => K.decl source
  | .seq _head _tail => K.seq source
  | .ite _cond _thenBranch _elseBranch => K.ite source
  | .whileStmt _cond _loopBody => K.whileStmt source
  | .block _blockBody => K.block source
  | .jump _j => K.jump source

/-- Turn function-body cases into the existing classifier-realization object. -/
def toRealization
    (K : FunctionBodyClassificationCases) :
    FunctionBodyClassifierRealization where
  classify := K.classify

end FunctionBodyClassificationCases

/-- Full-syntax classification kernel with already packaged loop behavior. -/
structure ClassificationKernel : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior : Source.LoopBehaviorCertificateTheorem
  stmt : StmtClassificationCases
  block : BlockClassificationCases
  functionBody : FunctionBodyClassificationCases

namespace ClassificationKernel

/-- Realized statement classifier produced by the full-syntax kernel. -/
def stmtRealization
    (K : ClassificationKernel) :
    StmtClassifierRealization :=
  K.stmt.toRealization

/-- Realized block classifier produced by the full-syntax kernel. -/
def blockRealization
    (K : ClassificationKernel) :
    BlockClassifierRealization :=
  K.block.toRealization

/-- Realized function-body classifier produced by the full-syntax kernel. -/
def functionBodyRealization
    (K : ClassificationKernel) :
    FunctionBodyClassifierRealization :=
  K.functionBody.toRealization

/-- Assemble the existing classification-realization theorem bundle. -/
def toClassificationRealizationTheorems
    (K : ClassificationKernel) :
    ClassificationRealizationTheorems :=
  classificationRealizationTheorems_of_classifiers
    K.stmtRealization
    K.blockRealization
    K.functionBodyRealization

/-- Assemble the named classification source theorem bundle. -/
def toClassificationSources
    (K : ClassificationKernel) :
    ClassificationRealizationSources where
  localControl := K.localControl
  scopeExit := K.scopeExit
  loopBehavior := K.loopBehavior
  classification := K.toClassificationRealizationTheorems

/-- Assemble the final closed-internal provider sources. -/
def toProviderSources
    (K : ClassificationKernel) :
    Source.ClosedInternalProviderSources :=
  K.toClassificationSources.toProviderSources

end ClassificationKernel

/-- Full-syntax classification kernel where while behavior is supplied by the
lower component certifier. -/
structure ComponentClassificationKernel : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorComponentSource Γ Γc σ cond body
  stmt : StmtClassificationCases
  block : BlockClassificationCases
  functionBody : FunctionBodyClassificationCases

namespace ComponentClassificationKernel

/-- Convert the component-level kernel into the ordinary kernel. -/
def toClassificationKernel
    (K : ComponentClassificationKernel) :
    ClassificationKernel where
  localControl := K.localControl
  scopeExit := K.scopeExit
  loopBehavior := loopBehaviorCertificateTheorem_of_componentTheorem K.loopBehavior
  stmt := K.stmt
  block := K.block
  functionBody := K.functionBody

/-- Assemble the final closed-internal provider sources. -/
def toProviderSources
    (K : ComponentClassificationKernel) :
    Source.ClosedInternalProviderSources :=
  K.toClassificationKernel.toProviderSources

end ComponentClassificationKernel

end Realize
end Soundness2
end Cpp3
