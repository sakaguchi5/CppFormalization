import CppFormalization.Cpp3.Soundness2.Realize.ClassificationFunctionBody

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Classification

Classification bundle layer for the linear Soundness2 route.

The intended order is:

1. local-control / scope-exit / loop-behavior theorem bundles are available;
2. boundary-level statement and block classifiers are available;
3. the function-body classifier is obtained from the statement classifier;
4. all classifiers are assembled into `ClassificationRealizationTheorems`;
5. the named `Source.ClassificationSourceTheorems` bundle is produced.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Lower classification realizer bundle consumed by provider construction. -/
structure ClassificationRealizationTheorems : Type where
  stmtClassify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Source.StmtBoundarySource Γ σ st →
        Source.ClosedStmtSoundness σ st
  blockClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.BlockBoundarySource Γ σ body →
        Source.ClosedBlockSoundness σ body
  functionBodyClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

/-- Bundle the three concrete source-level classifiers. -/
def classificationRealizationTheorems_of_classifiers
    (stmt : StmtClassifierRealization)
    (block : BlockClassifierRealization)
    (functionBody : FunctionBodyClassifierRealization) :
    ClassificationRealizationTheorems where
  stmtClassify := stmt.classify
  blockClassify := block.classify
  functionBodyClassify := functionBody.classify

/-- Assemble classification theorems from boundary-level statement/block classifiers. -/
def classificationRealizationTheorems_of_boundaryClassifiers
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization) :
    ClassificationRealizationTheorems :=
  classificationRealizationTheorems_of_classifiers
    stmt.toSourceRealization
    block.toSourceRealization
    (functionBodyRealization_of_boundaryStmtClassifier stmt)

/-- Complete realization source for the named classification source theorem bundle. -/
structure ClassificationRealizationSources : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior : Source.LoopBehaviorCertificateTheorem
  classification : ClassificationRealizationTheorems

namespace ClassificationRealizationSources

/-- Assemble the named classification source theorem bundle. -/
def toSourceTheorems
    (R : ClassificationRealizationSources) :
    Source.ClassificationSourceTheorems where
  localControl := R.localControl.toSourceTheorems
  scopeExit := R.scopeExit.toSourceTheorems
  loopBehavior := R.loopBehavior
  stmtClassify := R.classification.stmtClassify
  blockClassify := R.classification.blockClassify
  functionBodyClassify := R.classification.functionBodyClassify

end ClassificationRealizationSources

/-- Variant where loop behavior is supplied at the lower component level. -/
structure ClassificationComponentRealizationSources : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
        Σ Γc : TypeEnv,
          LoopBehaviorComponentSource Γ Γc σ cond body
  classification : ClassificationRealizationTheorems

namespace ClassificationComponentRealizationSources

/-- Convert the component-level loop behavior certifier into the ordinary bundle. -/
def toRealizationSources
    (R : ClassificationComponentRealizationSources) :
    ClassificationRealizationSources where
  localControl := R.localControl
  scopeExit := R.scopeExit
  loopBehavior := loopBehaviorCertificateTheorem_of_componentTheorem R.loopBehavior
  classification := R.classification

/-- Assemble the named classification source theorem bundle. -/
def toSourceTheorems
    (R : ClassificationComponentRealizationSources) :
    Source.ClassificationSourceTheorems :=
  R.toRealizationSources.toSourceTheorems

end ClassificationComponentRealizationSources

/-- Assemble a classification source theorem bundle from source-level classifiers. -/
def classificationSourceTheorems_of_classifiers
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (stmt : StmtClassifierRealization)
    (block : BlockClassifierRealization)
    (functionBody : FunctionBodyClassifierRealization) :
    Source.ClassificationSourceTheorems :=
  (ClassificationRealizationSources.mk
    localControl
    scopeExit
    loopBehavior
    (classificationRealizationTheorems_of_classifiers stmt block functionBody)).toSourceTheorems

/-- Assemble a classification source theorem bundle from boundary-level classifiers. -/
def classificationSourceTheorems_of_boundaryClassifiers
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization) :
    Source.ClassificationSourceTheorems :=
  (ClassificationRealizationSources.mk
    localControl
    scopeExit
    loopBehavior
    (classificationRealizationTheorems_of_boundaryClassifiers stmt block)).toSourceTheorems

/-- Assemble the named classification source theorem bundle from realized pieces. -/
def classificationSourceTheorems_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClassificationSourceTheorems :=
  (ClassificationRealizationSources.mk
    localControl scopeExit loopBehavior classification).toSourceTheorems

end Realize
end Soundness2
end Cpp3
