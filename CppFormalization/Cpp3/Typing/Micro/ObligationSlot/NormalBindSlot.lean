import CppFormalization.Cpp3.Typing.Micro.Composition.NormalBindStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.NormalBindSlot

Obligation slot for post-head statement continuation.

This file does not define a concrete C++ program contract such as read/write
noninterference.  It only records where such a contract is required: after a
normal head route, before entering the statement tail in the post-state.
-/

/-- A slot for the contract needed to continue from `head` to statement `tail`
after a normal runtime step from `σ` to `σ₁` and static environment transition
from `Γ` to `Θ`. -/
structure NormalBindContinuationSlot
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .normalBindContinuation
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace NormalBindContinuationSlot

/-- Extract the supplied program-facing obligation evidence. -/
def get
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (s : NormalBindContinuationSlot Γ Θ σ σ₁ head tail) : s.obligation :=
  s.evidence

end NormalBindContinuationSlot

end ObligationSlot
end Micro
end Typing
end Cpp3
