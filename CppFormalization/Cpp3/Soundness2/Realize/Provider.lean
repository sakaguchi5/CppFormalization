import CppFormalization.Cpp3.Soundness2.Realize.Classification

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Provider

Provider construction layer for the closed-internal Soundness2 route.

At this point the classification bundle has already been assembled.  This file
only packs it into the provider shape consumed by `Realize.ClosedInternal` and
`Final`.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Assemble closed-internal provider sources from a named classification theorem
bundle. -/
def providerSources_of_classification
    (classification : Source.ClassificationSourceTheorems) :
    Source.ClosedInternalProviderSources where
  classification := classification

/-- Assemble closed-internal provider sources from realized local-control,
scope-exit, loop-behavior, and lower classification theorem bundles. -/
def providerSources_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_classification
    (classificationSourceTheorems_of_realization
      localControl scopeExit loopBehavior classification)

/-- Assemble closed-internal provider sources directly from lower
control/scope/loop bundles by constructing the boundary-level classifiers first. -/
def providerSources_of_boundaryRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_classification
    (classificationSourceTheorems_of_boundaryRealization
      localControl scopeExit loopBehavior)

/-- Assemble closed-internal provider sources from boundary-level statement/block
classifiers.  The function-body classifier is derived after the boundary
statement classifier. -/
def providerSources_of_boundaryClassifiers
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_realization
    localControl
    scopeExit
    loopBehavior
    (classificationRealizationTheorems_of_boundaryClassifiers stmt block)

/-- Assemble closed-internal provider sources directly from a loop-behavior
component certifier. -/
def providerSources_of_componentRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body)
    (classification : ClassificationRealizationTheorems) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_realization
    localControl
    scopeExit
    (loopBehaviorCertificateTheorem_of_componentTheorem loopBehavior)
    classification

namespace ClassificationRealizationSources

/-- Assemble the closed-internal provider sources directly from classification
realization sources. -/
def toProviderSources
    (R : ClassificationRealizationSources) :
    Source.ClosedInternalProviderSources :=
  providerSources_of_classification R.toSourceTheorems

end ClassificationRealizationSources

namespace ClassificationComponentRealizationSources

/-- Assemble the closed-internal provider sources directly from component-level
classification realization sources. -/
def toProviderSources
    (R : ClassificationComponentRealizationSources) :
    Source.ClosedInternalProviderSources :=
  R.toRealizationSources.toProviderSources

end ClassificationComponentRealizationSources

end Realize
end Soundness2
end Cpp3
