import CppFormalization.Cpp3.Typing.Micro.Composition.BlockConsStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.BlockConsSlot

Obligation slot for block-tail boundary preservation.

This is the block-body analogue of `StatementTailBoundarySlot`: after a normal
head statement in a block body, the remaining block body is the next statically
typed program point.

The C++ block-cons routing rule

  head normal → execute remaining block body

belongs to Semantics.  This slot only records the practical C++ obligation that
the post-head runtime state still satisfies the boundary needed to enter the
block tail.
-/

/-- A slot for the contract needed to continue from block-body `head` to block
`tail` after a normal runtime step from `σ` to `σ₁` and static environment
transition from `Γ` to `Θ`.

The concrete obligation is intentionally abstract here.  Later Boundary/Stability
layers may instantiate it with the appropriate tail-block boundary preservation
fact.
-/
structure BlockTailBoundarySlot
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  kind : Contracts.ContractKind :=
    .obligation .tailBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace BlockTailBoundarySlot

/-- Extract the supplied program-facing block-tail-boundary obligation evidence. -/
def get
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (s : BlockTailBoundarySlot Γ Θ σ σ₁ head tail) : s.obligation :=
  s.evidence

end BlockTailBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
