import CppFormalization.Cpp3.Typing.Micro.Composition.NormalBindStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.NormalBindSlot

Obligation slot for statement-tail boundary preservation.

The static normal-bind component says that, after a normal head route, the tail
is the next statically typed statement.  Runtime layers still need evidence that
the head execution did not destroy the boundary needed to enter the tail in the
post-state.

This is not the C++ sequencing rule itself.  The semantic rule

  head normal → execute tail

belongs to Semantics.  This slot only names the practical C++ obligation that the
post-head state still satisfies the tail boundary.

For example, this obligation fails for code shaped like:

  p = nullptr;
  *p = 1;

unless additional evidence explains why the tail dereference is still safe.
-/

/-- A slot for the contract needed to continue from `head` to statement `tail`
after a normal runtime step from `σ` to `σ₁` and static environment transition
from `Γ` to `Θ`.

The concrete obligation is intentionally abstract here.  Later Boundary/Stability
layers may instantiate it with read/write footprint separation, dereference
preservation, condition-boundary preservation, or another tail-boundary theorem.
-/
structure StatementTailBoundarySlot
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .tailBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace StatementTailBoundarySlot

/-- Extract the supplied program-facing tail-boundary obligation evidence. -/
def get
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (s : StatementTailBoundarySlot Γ Θ σ σ₁ head tail) : s.obligation :=
  s.evidence

end StatementTailBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
