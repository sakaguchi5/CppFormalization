import CppFormalization.Cpp3.Effects.Scope
import CppFormalization.Cpp3.Semantics.SelectedRoute.Basic

/-!
# CppFormalization.Cpp3.Effects.Flow

Effect surfaces around selected control-flow points.

This layer names what the selected head/condition/body may touch.  It does not
state non-interference and it does not rebuild a post-state Boundary; those are
Stability and Continuation responsibilities.
-/

namespace Cpp3
namespace Effects

/-- Effect surface for the head of `head; tail`, paired with the static tail
entry that later continuation will need. -/
structure SeqHeadEffectSurface
    (Γ Θ : TypeEnv) (head tail : CppStmt) : Type where
  headEffect : StmtEffect Γ head
  tailStatic : Static.StaticSeqTailBoundaryInfo Γ Θ head tail

namespace SeqHeadEffectSurface

def headReadsName
    {Γ Θ : TypeEnv} {head tail : CppStmt}
    (h : SeqHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.readsName

def headWritesDirectName
    {Γ Θ : TypeEnv} {head tail : CppStmt}
    (h : SeqHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.writesDirectName

def headBindsName
    {Γ Θ : TypeEnv} {head tail : CppStmt}
    (h : SeqHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.bindsName

end SeqHeadEffectSurface

/-- Effect surface for the head of a block cons. -/
structure BlockHeadEffectSurface
    (Γ Θ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Type where
  headEffect : StmtEffect Γ head
  tailStatic : Static.StaticBlockTailBoundaryInfo Γ Θ head tail

namespace BlockHeadEffectSurface

def headReadsName
    {Γ Θ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.readsName

def headWritesDirectName
    {Γ Θ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.writesDirectName

def headBindsName
    {Γ Θ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockHeadEffectSurface Γ Θ head tail) : NameSet :=
  h.headEffect.bindsName

end BlockHeadEffectSurface

/-- Effect surface for evaluating a branch condition and exposing the statically
selected branch entry. -/
structure SelectedBranchEffectSurface
    (Γ Γc : TypeEnv) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  condEffect : CondEffect Γ Γc cond
  branchStatic : Static.StaticSelectedBranchBoundaryInfo Γ Γc cond thenBranch elseBranch

namespace SelectedBranchEffectSurface

def conditionReadsName
    {Γ Γc : TypeEnv} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (h : SelectedBranchEffectSurface Γ Γc cond thenBranch elseBranch) : NameSet :=
  h.condEffect.readsName

def conditionDerefUse
    {Γ Γc : TypeEnv} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (h : SelectedBranchEffectSurface Γ Γc cond thenBranch elseBranch) : Prop :=
  h.condEffect.derefUse

end SelectedBranchEffectSurface

/-- Effect surface for one while boundary step: condition plus body entry. -/
structure WhileEffectSurface
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  condEffect : CondEffect Γ Γc cond
  bodyEffect : StmtEffect Γc body
  backedgeStatic : Static.StaticWhileBackedgeBoundaryInfo Γ Γc cond body

namespace WhileEffectSurface

def conditionReadsName
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileEffectSurface Γ Γc cond body) : NameSet :=
  h.condEffect.readsName

def bodyReadsName
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileEffectSurface Γ Γc cond body) : NameSet :=
  h.bodyEffect.readsName

def bodyWritesDirectName
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileEffectSurface Γ Γc cond body) : NameSet :=
  h.bodyEffect.writesDirectName

def bodyBindsName
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileEffectSurface Γ Γc cond body) : NameSet :=
  h.bodyEffect.bindsName

end WhileEffectSurface

/-- Effect surface for entering an opened block body. -/
structure OpenedBlockEffectSurface
    (Γ Γopen : TypeEnv) (body : StmtBlock) : Type where
  openedStatic : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body
  bodyEffect : BlockEffect Γopen body

namespace OpenedBlockEffectSurface

def bodyReadsName
    {Γ Γopen : TypeEnv} {body : StmtBlock}
    (h : OpenedBlockEffectSurface Γ Γopen body) : NameSet :=
  h.bodyEffect.readsName

def bodyWritesDirectName
    {Γ Γopen : TypeEnv} {body : StmtBlock}
    (h : OpenedBlockEffectSurface Γ Γopen body) : NameSet :=
  h.bodyEffect.writesDirectName

def bodyBindsName
    {Γ Γopen : TypeEnv} {body : StmtBlock}
    (h : OpenedBlockEffectSurface Γ Γopen body) : NameSet :=
  h.bodyEffect.bindsName

end OpenedBlockEffectSurface

/-- Runtime route plus effect surface for a sequence normal route.

The route is semantic evidence; the effect surface remains static/syntactic.  No
post-state continuation safety is claimed here. -/
structure RoutedSeqHeadEffect
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  route : Semantics.SeqNormalRoute σ σ₁ head tail
  effects : SeqHeadEffectSurface Γ Θ head tail

/-- Runtime route plus effect surface for a block-cons normal route. -/
structure RoutedBlockHeadEffect
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  route : Semantics.BlockConsNormalRoute σ σ₁ head tail
  effects : BlockHeadEffectSurface Γ Θ head tail

end Effects
end Cpp3
