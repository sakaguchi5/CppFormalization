import CppFormalization.Cpp3.Soundness2.Realize.Provider

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Classification

Realization helpers for the Soundness2 classification layer.

`Source.ClassificationSourceTheorems` is the remaining theorem surface that turns
closed-internal boundary sources into statement/block/function-body
classification.  This file does not pretend to solve that classification problem
magically; instead it gives a clean realization layer for assembling the
classification source bundle from smaller realized pieces.

The intended direction is:

* local-control realization theorems;
* scope-exit realization theorems;
* loop-behavior certificate theorem, or a lower behavior-component certifier;
* concrete statement/block/function-body classifiers;

assemble into the provider source consumed by `Soundness2.Final`.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realized classifier for closed-internal statements. -/
structure StmtClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Source.StmtBoundarySource Γ σ st →
        Source.ClosedStmtSoundness σ st

/-- Realized classifier for closed-internal block bodies. -/
structure BlockClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.BlockBoundarySource Γ σ body →
        Source.ClosedBlockSoundness σ body

/-- Realized classifier for closed-internal function bodies. -/
structure FunctionBodyClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

/-- Bundle the three concrete classifiers into the realization object already
expected by `Realize.Provider`. -/
def classificationRealizationTheorems_of_classifiers
    (stmt : StmtClassifierRealization)
    (block : BlockClassifierRealization)
    (functionBody : FunctionBodyClassifierRealization) :
    ClassificationRealizationTheorems where
  stmtClassify := stmt.classify
  blockClassify := block.classify
  functionBodyClassify := functionBody.classify

/-- Complete realization source for the named classification source theorem
bundle. -/
structure ClassificationRealizationSources : Type where
  localControl : LocalControlRealizationTheorems
  scopeExit : ScopeExitRealizationTheorems
  loopBehavior : Source.LoopBehaviorCertificateTheorem
  classification : ClassificationRealizationTheorems

namespace ClassificationRealizationSources

/-- Assemble the named classification source theorem bundle. -/
def toSourceTheorems
    (R : ClassificationRealizationSources) :
    Source.ClassificationSourceTheorems :=
  classificationSourceTheorems_of_realization
    R.localControl
    R.scopeExit
    R.loopBehavior
    R.classification

/-- Assemble the closed-internal provider sources directly from realized
classification sources. -/
def toProviderSources
    (R : ClassificationRealizationSources) :
    Source.ClosedInternalProviderSources where
  classification := R.toSourceTheorems

end ClassificationRealizationSources

/-- Variant where loop behavior is supplied at the lower component level rather
than already as a `LoopBehaviorCertificateTheorem`. -/
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

/-- Convert the component-level loop behavior certifier into the ordinary
classification realization source. -/
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

/-- Assemble the closed-internal provider sources directly from component-level
realization sources. -/
def toProviderSources
    (R : ClassificationComponentRealizationSources) :
    Source.ClosedInternalProviderSources :=
  R.toRealizationSources.toProviderSources

end ClassificationComponentRealizationSources

/-- Assemble a classification source theorem bundle from the split classifier
objects. -/
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

/-- Assemble closed-internal provider sources from split classifier objects. -/
def providerSources_of_classifiers
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (stmt : StmtClassifierRealization)
    (block : BlockClassifierRealization)
    (functionBody : FunctionBodyClassifierRealization) :
    Source.ClosedInternalProviderSources where
  classification :=
    classificationSourceTheorems_of_classifiers
      localControl scopeExit loopBehavior stmt block functionBody

/-- Assemble closed-internal provider sources from split classifier objects and a
component-level loop behavior certifier. -/
def providerSources_of_componentClassifiers
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    (stmt : StmtClassifierRealization)
    (block : BlockClassifierRealization)
    (functionBody : FunctionBodyClassifierRealization) :
    Source.ClosedInternalProviderSources :=
  (ClassificationComponentRealizationSources.mk
    localControl
    scopeExit
    loopBehavior
    (classificationRealizationTheorems_of_classifiers stmt block functionBody)).toProviderSources

end Realize
end Soundness2
end Cpp3
