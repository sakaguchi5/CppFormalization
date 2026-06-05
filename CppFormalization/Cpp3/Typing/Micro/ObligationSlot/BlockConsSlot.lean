import CppFormalization.Cpp3.Typing.Micro.Composition.BlockConsStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.BlockConsSlot

Obligation slot for post-head block-tail continuation.

This is the block-body analogue of `NormalBindContinuationSlot`: after a normal
head statement, the remaining block body may require a programmer-facing
stability contract before it can be entered in the post-state.
-/

/-- A slot for the contract needed to continue from block-body `head` to block
`tail` after a normal runtime step from `σ` to `σ₁` and static environment
transition from `Γ` to `Θ`. -/
structure BlockConsContinuationSlot
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  kind : Contracts.ContractKind :=
    .obligation .blockConsContinuation
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace BlockConsContinuationSlot

/-- Extract the supplied program-facing obligation evidence. -/
def get
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (s : BlockConsContinuationSlot Γ Θ σ σ₁ head tail) : s.obligation :=
  s.evidence

end BlockConsContinuationSlot

end ObligationSlot
end Micro
end Typing
end Cpp3
