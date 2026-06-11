import CppFormalization.Cpp3.Soundness2.Realize.BoundarySource
import CppFormalization.Cpp3.Soundness2.Source.Stability

/-!
# CppFormalization.Cpp3.Soundness2.Realize.Stability

Lower-evidence realization of stability packages for the closed-internal
Soundness2 route.

This layer restores the C++ control-boundary obligations below the final route:
seq tails, block tails, selected branches, while backedges, opened blocks, and
block scope close.  Later local-control and scope-exit theorem bundles consume
these stability packages.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Turn a certified proposition into the stability certificate expected by the
Stability layer. -/
def stabilityCertificate_of_certified
    {stable : Prop}
    (evidence : Contracts.Certified stable) :
    Stability.StabilityCertificate .stabilityDerived stable where
  evidence := evidence

/-- Realize sequence-tail boundary source from lower components. -/
def seqTailBoundarySource_of_components
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.seq head tail))
    (route : Semantics.SeqNormalRoute σ σ₁ head tail)
    (surface : Effects.SeqHeadEffectSurface Γ Θ head tail)
    (preserved : SafetyFragment.TailBoundaryFootprintPreserved Γ Θ head tail)
    (tailBoundary : Boundary.StmtBoundary Θ σ₁ tail) :
    Source.SeqTailBoundarySource Γ Θ σ σ₁ head tail where
  source := source
  route := route
  surface := surface
  preserved := preserved
  tail := tailBoundary

/-- Realize sequence-tail stability from lower components plus a certified
stability theorem. -/
def seqTailStability_of_components
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.seq head tail))
    (route : Semantics.SeqNormalRoute σ σ₁ head tail)
    (surface : Effects.SeqHeadEffectSurface Γ Θ head tail)
    (preserved : SafetyFragment.TailBoundaryFootprintPreserved Γ Θ head tail)
    (tailBoundary : Boundary.StmtBoundary Θ σ₁ tail)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.SeqTailStability Γ Θ σ σ₁ head tail :=
  (seqTailBoundarySource_of_components source route surface preserved tailBoundary).toStability
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize block-tail boundary source from lower components. -/
def blockTailBoundarySource_of_components
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (source : Boundary.BlockBoundary Γ σ (.cons head tail))
    (route : Semantics.BlockConsNormalRoute σ σ₁ head tail)
    (surface : Effects.BlockHeadEffectSurface Γ Θ head tail)
    (preserved : SafetyFragment.BlockTailBoundaryFootprintPreserved Γ Θ head tail)
    (tailBoundary : Boundary.BlockBoundary Θ σ₁ tail) :
    Source.BlockTailBoundarySource Γ Θ σ σ₁ head tail where
  source := source
  route := route
  surface := surface
  preserved := preserved
  tail := tailBoundary

/-- Realize block-tail stability from lower components plus a certified stability
theorem. -/
def blockTailStability_of_components
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (source : Boundary.BlockBoundary Γ σ (.cons head tail))
    (route : Semantics.BlockConsNormalRoute σ σ₁ head tail)
    (surface : Effects.BlockHeadEffectSurface Γ Θ head tail)
    (preserved : SafetyFragment.BlockTailBoundaryFootprintPreserved Γ Θ head tail)
    (tailBoundary : Boundary.BlockBoundary Θ σ₁ tail)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.BlockTailStability Γ Θ σ σ₁ head tail :=
  (blockTailBoundarySource_of_components source route surface preserved tailBoundary).toStability
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize selected then-branch boundary source. -/
def selectedThenBoundarySource_of_components
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
    (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .thenBranch)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
      thenBranch elseBranch)
    (branch : Boundary.StmtBoundary Γc σc thenBranch) :
    Source.SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch .thenBranch :=
  Source.SelectedBranchBoundarySource.thenBoundary source route condition preserved branch

/-- Realize selected else-branch boundary source. -/
def selectedElseBoundarySource_of_components
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
    (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .elseBranch)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
      thenBranch elseBranch)
    (branch : Boundary.StmtBoundary Γc σc elseBranch) :
    Source.SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch .elseBranch :=
  Source.SelectedBranchBoundarySource.elseBoundary source route condition preserved branch

/-- Realize selected then-branch stability. -/
def selectedThenStability_of_components
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
    (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .thenBranch)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
      thenBranch elseBranch)
    (branch : Boundary.StmtBoundary Γc σc thenBranch)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch .thenBranch :=
  (selectedThenBoundarySource_of_components source route condition preserved branch).toStability
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize selected else-branch stability. -/
def selectedElseStability_of_components
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
    (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .elseBranch)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
      thenBranch elseBranch)
    (branch : Boundary.StmtBoundary Γc σc elseBranch)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch .elseBranch :=
  (selectedElseBoundarySource_of_components source route condition preserved branch).toStability
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize while-boundary source from lower components. -/
def whileBoundarySource_of_components
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.whileStmt cond body))
    (route : Semantics.WhileBoundaryRoute σ cond body)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (surface : Effects.WhileEffectSurface Γ Γc cond body)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (backedgeBoundary : Prop)
    (backedgeEvidence : Contracts.Requires backedgeBoundary) :
    Source.WhileBoundarySource Γ Γc σ cond body where
  source := source
  route := route
  condition := condition
  surface := surface
  loopSafety := loopSafety
  backedgeBoundary := backedgeBoundary
  backedgeEvidence := backedgeEvidence

/-- Realize while-boundary stability from lower components plus certified evidence. -/
def whileBoundaryStability_of_components
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (source : Boundary.StmtBoundary Γ σ (.whileStmt cond body))
    (route : Semantics.WhileBoundaryRoute σ cond body)
    (condition : Boundary.CondBoundary Γ Γc σ cond)
    (surface : Effects.WhileEffectSurface Γ Γc cond body)
    (loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body)
    (backedgeBoundary : Prop)
    (backedgeEvidence : Contracts.Requires backedgeBoundary)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.WhileBoundaryStability Γ Γc σ cond body :=
  (whileBoundarySource_of_components source route condition surface loopSafety
      backedgeBoundary backedgeEvidence).toStability
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize opened-block boundary source. -/
def openedBlockBoundarySource_of_components
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body)
    (effect : Effects.OpenedBlockEffectSurface Γ Γopen body)
    (route : Semantics.OpenedBlockRoute σ σopened body)
    (bodyBoundary : Boundary.BlockBoundary Γopen σopened body) :
    Source.OpenedBlockBoundarySource Γ Γopen σ σopened body where
  static := static
  effect := effect
  route := route
  bodyBoundary := bodyBoundary

/-- Realize opened-block stability. -/
def openedBlockStability_of_components
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (source : Boundary.StmtBoundary Γ σ (.block body))
    (static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body)
    (effect : Effects.OpenedBlockEffectSurface Γ Γopen body)
    (route : Semantics.OpenedBlockRoute σ σopened body)
    (bodyBoundary : Boundary.BlockBoundary Γopen σopened body)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.OpenedBlockStability Γ Γopen σ σopened body :=
  (openedBlockBoundarySource_of_components static effect route bodyBoundary).toStability
    source
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize block-scope boundary source. -/
def blockScopeBoundarySource_of_components
    {Γ Γopen Θ Δ : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (effect : Effects.BlockScopeEffect Γ Γopen Θ Δ body)
    (opened : Boundary.OpenedBlockBoundary Γ Γopen σ σopened body)
    (closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body) :
    Source.BlockScopeBoundarySource Γ Γopen Θ Δ σ σopened body where
  effect := effect
  opened := opened
  closeSafe := closeSafe

/-- Realize block-scope-open stability. -/
def blockScopeOpenStability_of_components
    {Γ Γopen Θ Δ : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (effect : Effects.BlockScopeEffect Γ Γopen Θ Δ body)
    (opened : Boundary.OpenedBlockBoundary Γ Γopen σ σopened body)
    (closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body)
    (openedStable : Stability.OpenedBlockStability Γ Γopen σ σopened body)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.BlockScopeOpenStability Γ Γopen Θ Δ σ σopened body :=
  (blockScopeBoundarySource_of_components effect opened closeSafe).toOpenStability
    openedStable
    stable
    (stabilityCertificate_of_certified evidence)

/-- Realize block-close boundary source. -/
def blockCloseBoundarySource_of_components
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body)
    (closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body)
    (closeStep : popScope? σbody = some σclosed) :
    Source.BlockCloseBoundarySource Γ Γopen Θ Δ σbody σclosed body where
  closeEffect := closeEffect
  closeSafe := closeSafe
  closeStep := closeStep

/-- Realize block-close stability. -/
def blockCloseStability_of_components
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body)
    (closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body)
    (closeStep : popScope? σbody = some σclosed)
    (stable : Prop)
    (evidence : Contracts.Certified stable) :
    Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body :=
  (blockCloseBoundarySource_of_components closeEffect closeSafe closeStep).toStability
    stable
    (stabilityCertificate_of_certified evidence)

end Realize
end Soundness2
end Cpp3
