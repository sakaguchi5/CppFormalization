import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Provider

Provider construction layer for Soundness2.

This file keeps the objects that are still abstract inputs to the final
closed-internal soundness theorem.  A provider is not a C++ runtime object; it is
an explicitly named bundle of proof components needed to classify closed
statements, blocks, and function bodies.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realizer bundle for all local-control source theorems. -/
structure LocalControlRealizationTheorems : Type where
  seq : Source.SeqTailControlSourceTheorem
  blockTail : Source.BlockTailControlSourceTheorem
  branch : Source.SelectedBranchControlSourceTheorem
  whileBody : Source.LoopBodyEntryControlSourceTheorem
  whileBackedge : Source.LoopBackedgeControlSourceTheorem

namespace LocalControlRealizationTheorems

/-- Convert realized local-control theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : LocalControlRealizationTheorems) :
    Source.LocalControlSourceTheorems where
  seq := R.seq
  blockTail := R.blockTail
  branch := R.branch
  whileBody := R.whileBody
  whileBackedge := R.whileBackedge

end LocalControlRealizationTheorems

/-- Realizer bundle for scope-exit source theorems. -/
structure ScopeExitRealizationTheorems : Type where
  blockClose : Source.BlockCloseSourceTheorem

namespace ScopeExitRealizationTheorems

/-- Convert realized scope-exit theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : ScopeExitRealizationTheorems) :
    Source.ScopeExitSourceTheorems where
  blockClose := R.blockClose

end ScopeExitRealizationTheorems

/-- Lower realization source for a while behavior certificate. -/
structure LoopBehaviorComponentSource
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  condition : Boundary.CondBoundary Γ Γc σ cond
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  behavior : Source.LoopBehaviorSource σ cond body

namespace LoopBehaviorComponentSource

/-- Convert lower loop-behavior components into the behavior certificate. -/
def toCertificate
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificate Γ Γc σ cond body where
  condition := h.condition
  loopSafety := h.loopSafety
  behavior := h.behavior

end LoopBehaviorComponentSource

/-- Build the loop-behavior theorem from a lower behavior-component certifier. -/
def loopBehaviorCertificateTheorem_of_componentTheorem
    (certify :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
          Σ Γc : TypeEnv,
            LoopBehaviorComponentSource Γ Γc σ cond body) :
    Source.LoopBehaviorCertificateTheorem where
  certify := by
    intro Γ σ cond body boundary
    rcases certify boundary with ⟨Γc, source⟩
    exact ⟨Γc, source.toCertificate⟩

/-- Lower classification realizer bundle. -/
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

/-- Assemble the named classification source theorem bundle. -/
def classificationSourceTheorems_of_realization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    (classification : ClassificationRealizationTheorems) :
    Source.ClassificationSourceTheorems where
  localControl := localControl.toSourceTheorems
  scopeExit := scopeExit.toSourceTheorems
  loopBehavior := loopBehavior
  stmtClassify := classification.stmtClassify
  blockClassify := classification.blockClassify
  functionBodyClassify := classification.functionBodyClassify

end Realize
end Soundness2
end Cpp3
