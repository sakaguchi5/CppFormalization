import CppFormalization.Cpp3.Soundness2.Source.Boundary
import CppFormalization.Cpp3.Stability.All

/-!
# CppFormalization.Cpp3.Soundness2.Source.Stability

Source vocabulary for selected post-state boundaries and stability packages.

These sources expose the selected semantic route, the effect/safety surface, and
the post-state boundary.  Stability itself is built only after a certified
stability proposition is supplied.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Boundary source for a sequence tail after a normally completed head. -/
structure SeqTailBoundarySource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.seq head tail)
  route : Semantics.SeqNormalRoute σ σ₁ head tail
  surface : Effects.SeqHeadEffectSurface Γ Θ head tail
  preserved : SafetyFragment.TailBoundaryFootprintPreserved Γ Θ head tail
  tail : Boundary.StmtBoundary Θ σ₁ tail

namespace SeqTailBoundarySource

/-- Build the selected sequence-tail boundary. -/
def toBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailBoundarySource Γ Θ σ σ₁ head tail) :
    Boundary.SeqTailBoundary Γ Θ σ σ₁ head tail where
  route := h.route
  surface := h.surface
  preserved := h.preserved
  tail := h.tail

/-- Package the selected sequence-tail boundary as stability evidence. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailBoundarySource Γ Θ σ σ₁ head tail)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.SeqTailStability Γ Θ σ σ₁ head tail where
  source := h.source
  target := h.toBoundary
  stable := stable
  certificate := certificate

end SeqTailBoundarySource

/-- Boundary source for a block tail after a normally completed block head. -/
structure BlockTailBoundarySource
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  source : Boundary.BlockBoundary Γ σ (.cons head tail)
  route : Semantics.BlockConsNormalRoute σ σ₁ head tail
  surface : Effects.BlockHeadEffectSurface Γ Θ head tail
  preserved : SafetyFragment.BlockTailBoundaryFootprintPreserved Γ Θ head tail
  tail : Boundary.BlockBoundary Θ σ₁ tail

namespace BlockTailBoundarySource

/-- Build the selected block-tail boundary. -/
def toBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailBoundarySource Γ Θ σ σ₁ head tail) :
    Boundary.BlockTailBoundary Γ Θ σ σ₁ head tail where
  route := h.route
  surface := h.surface
  preserved := h.preserved
  tail := h.tail

/-- Package the selected block-tail boundary as stability evidence. -/
def toStability
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailBoundarySource Γ Θ σ σ₁ head tail)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.BlockTailStability Γ Θ σ σ₁ head tail where
  source := h.source
  target := h.toBoundary
  stable := stable
  certificate := certificate

end BlockTailBoundarySource

/-- Boundary source for an if-statement selected branch. -/
inductive SelectedBranchBoundarySource
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Semantics.BranchSide → Type where
  | thenBoundary
      (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
      (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch
        .thenBranch)
      (condition : Boundary.CondBoundary Γ Γc σ cond)
      (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
        thenBranch elseBranch)
      (branch : Boundary.StmtBoundary Γc σc thenBranch) :
      SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch .thenBranch
  | elseBoundary
      (source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
      (route : Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch
        .elseBranch)
      (condition : Boundary.CondBoundary Γ Γc σ cond)
      (preserved : SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond
        thenBranch elseBranch)
      (branch : Boundary.StmtBoundary Γc σc elseBranch) :
      SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch .elseBranch

namespace SelectedBranchBoundarySource

/-- Project the source if-statement boundary. -/
def source
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch side) :
    Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) :=
  match h with
  | .thenBoundary source _ _ _ _ => source
  | .elseBoundary source _ _ _ _ => source

/-- Build the selected branch boundary. -/
def toBoundary
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch side) :
    Boundary.SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch side :=
  match h with
  | .thenBoundary _ route condition preserved branch =>
      Boundary.SelectedBranchBoundary.thenBoundary route condition preserved branch
  | .elseBoundary _ route condition preserved branch =>
      Boundary.SelectedBranchBoundary.elseBoundary route condition preserved branch

/-- Package the selected branch boundary as stability evidence. -/
def toStability
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchBoundarySource Γ Γc σ σc cond thenBranch elseBranch side)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side where
  source := h.source
  target := h.toBoundary
  stable := stable
  certificate := certificate

end SelectedBranchBoundarySource

/-- Boundary source for a selected while route. -/
structure WhileBoundarySource
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  route : Semantics.WhileBoundaryRoute σ cond body
  condition : Boundary.CondBoundary Γ Γc σ cond
  surface : Effects.WhileEffectSurface Γ Γc cond body
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  backedgeBoundary : Prop
  backedgeEvidence : Contracts.Requires backedgeBoundary

namespace WhileBoundarySource

/-- Build the selected while boundary. -/
def toBoundary
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundarySource Γ Γc σ cond body) :
    Boundary.WhileBoundary Γ Γc σ cond body where
  route := h.route
  condition := h.condition
  surface := h.surface
  loopSafety := h.loopSafety
  backedgeBoundary := h.backedgeBoundary
  backedgeEvidence := h.backedgeEvidence

/-- Package the selected while boundary as stability evidence. -/
def toStability
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundarySource Γ Γc σ cond body)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.WhileBoundaryStability Γ Γc σ cond body where
  source := h.source
  target := h.toBoundary
  stable := stable
  certificate := certificate

end WhileBoundarySource

/-- Source for an opened block-body boundary. -/
structure OpenedBlockBoundarySource
    (Γ Γopen : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body
  effect : Effects.OpenedBlockEffectSurface Γ Γopen body
  route : Semantics.OpenedBlockRoute σ σopened body
  bodyBoundary : Boundary.BlockBoundary Γopen σopened body

namespace OpenedBlockBoundarySource

/-- Build the opened-block boundary. -/
def toBoundary
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockBoundarySource Γ Γopen σ σopened body) :
    Boundary.OpenedBlockBoundary Γ Γopen σ σopened body where
  static := h.static
  effect := h.effect
  route := h.route
  bodyBoundary := h.bodyBoundary

/-- Build the routed opened-block boundary. -/
def toRoutedBoundary
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockBoundarySource Γ Γopen σ σopened body) :
    Boundary.RoutedOpenedBlockBoundary Γ Γopen σ σopened body where
  route := h.route
  boundary := h.toBoundary

/-- Package opened-block entry as stability evidence. -/
def toStability
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (source : Boundary.StmtBoundary Γ σ (.block body))
    (h : OpenedBlockBoundarySource Γ Γopen σ σopened body)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.OpenedBlockStability Γ Γopen σ σopened body where
  source := source
  target := h.toRoutedBoundary
  stable := stable
  certificate := certificate

end OpenedBlockBoundarySource

/-- Source for the block scope boundary connecting opening and closing surfaces. -/
structure BlockScopeBoundarySource
    (Γ Γopen Θ Δ : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  effect : Effects.BlockScopeEffect Γ Γopen Θ Δ body
  opened : Boundary.OpenedBlockBoundary Γ Γopen σ σopened body
  closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body

namespace BlockScopeBoundarySource

/-- Build the block-scope boundary. -/
def toBoundary
    {Γ Γopen Θ Δ : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : BlockScopeBoundarySource Γ Γopen Θ Δ σ σopened body) :
    Boundary.BlockScopeBoundary Γ Γopen Θ Δ σ σopened body where
  effect := h.effect
  opened := h.opened
  closeSafe := h.closeSafe

/-- Package block-scope opening as stability evidence. -/
def toOpenStability
    {Γ Γopen Θ Δ : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : BlockScopeBoundarySource Γ Γopen Θ Δ σ σopened body)
    (openedStable : Stability.OpenedBlockStability Γ Γopen σ σopened body)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.BlockScopeOpenStability Γ Γopen Θ Δ σ σopened body where
  boundary := h.toBoundary
  openedStable := openedStable
  stable := stable
  certificate := certificate

end BlockScopeBoundarySource

/-- Source for closing a block scope after the opened body has produced a state. -/
structure BlockCloseBoundarySource
    (Γ Γopen Θ Δ : TypeEnv) (σbody σclosed : State) (body : StmtBlock) : Type where
  closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body
  closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body
  closeStep : popScope? σbody = some σclosed

namespace BlockCloseBoundarySource

/-- Build the concrete block-close boundary. -/
def toBoundary
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseBoundarySource Γ Γopen Θ Δ σbody σclosed body) :
    Boundary.BlockCloseBoundary Γ Γopen Θ Δ σbody σclosed body where
  closeEffect := h.closeEffect
  closeSafe := h.closeSafe
  closeStep := h.closeStep

/-- Package block-close as stability evidence. -/
def toStability
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseBoundarySource Γ Γopen Θ Δ σbody σclosed body)
    (stable : Prop)
    (certificate : Stability.StabilityCertificate .stabilityDerived stable) :
    Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body where
  close := h.toBoundary
  stable := stable
  certificate := certificate

end BlockCloseBoundarySource

end Source
end Soundness2
end Cpp3
