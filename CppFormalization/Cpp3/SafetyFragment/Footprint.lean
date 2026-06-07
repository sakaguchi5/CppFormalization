import CppFormalization.Cpp3.SafetyFragment.Core

/-!
# CppFormalization.Cpp3.SafetyFragment.Footprint

Footprint and non-interference safety obligations.

These structures name the practical C++ promise that a write/effect does not
invalidate a later read, condition, tail, branch, or block-body entry.
-/

namespace Cpp3
namespace SafetyFragment

/-- Reads required later are preserved across an effect. -/
structure ReadFootprintPreserved
    (before after : Effects.NameFootprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .readFootprintPreserved
  preserved : Contracts.Requires (Effects.subsetNameSet before.reads after.reads)

/-- A write footprint is separated from a later read footprint. -/
structure WriteFootprintSeparated
    (writer later : Effects.NameFootprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .writeFootprintSeparated
  separated : Contracts.Requires (Effects.disjointNameSet writer.writes later.reads)

/-- A combined read/write separation obligation. -/
structure ReadWriteFootprintSeparated
    (left right : Effects.NameFootprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .readWriteFootprintSeparated
  leftWriteRightRead : Contracts.Requires (Effects.disjointNameSet left.writes right.reads)
  rightWriteLeftRead : Contracts.Requires (Effects.disjointNameSet right.writes left.reads)

/-- Alias separation, intentionally abstract at this layer.

The Effects layer is mostly source-name based.  Concrete alias/address reasoning
belongs to Boundary/Stability, so this safety-fragment obligation carries an
explicit proposition. -/
structure AliasSeparated
    (left right : Effects.Footprint) : Type where
  kind : Contracts.ContractKind :=
    .obligation .aliasSeparated
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace AliasSeparated

def get
    {left right : Effects.Footprint}
    (h : AliasSeparated left right) : h.obligation :=
  h.evidence

end AliasSeparated

/-- A statement head does not invalidate the later statement tail. -/
structure TailBoundaryFootprintPreserved
    (Γ Θ : TypeEnv) (head tail : CppStmt) : Type where
  surface : Effects.SeqHeadEffectSurface Γ Θ head tail
  kind : Contracts.ContractKind :=
    .obligation .tailBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- A block head does not invalidate the later block tail. -/
structure BlockTailBoundaryFootprintPreserved
    (Γ Θ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Type where
  surface : Effects.BlockHeadEffectSurface Γ Θ head tail
  kind : Contracts.ContractKind :=
    .obligation .tailBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- Condition evaluation does not invalidate the selected branch boundary. -/
structure BranchBoundaryAfterConditionPreserved
    (Γ Γc : TypeEnv) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  surface : Effects.SelectedBranchEffectSurface Γ Γc cond thenBranch elseBranch
  kind : Contracts.ContractKind :=
    .obligation .branchBoundaryAfterCondition
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- Entering an opened block body preserves the static opened-body boundary. -/
structure OpenedBlockBodyBoundaryPreserved
    (Γ Γopen : TypeEnv) (body : StmtBlock) : Type where
  surface : Effects.OpenedBlockEffectSurface Γ Γopen body
  kind : Contracts.ContractKind :=
    .obligation .openedBlockBodyBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

end SafetyFragment
end Cpp3
