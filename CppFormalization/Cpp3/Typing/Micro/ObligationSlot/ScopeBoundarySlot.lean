import CppFormalization.Cpp3.Typing.Micro.Composition.ScopeBoundaryStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.ScopeBoundarySlot

Obligation slot for opened block-body boundaries.

The static block component opens a type scope and checks the block body there.
Runtime proofs additionally need a boundary/adequacy object for the opened body
and a safe exit back to the outer scope.  This slot names that requirement
without baking it into typing.
-/

/-- A slot for the contract needed to move between a block statement boundary and
its opened block-body boundary. -/
structure ScopeBoundarySlot
    (Γ Γopen : TypeEnv) (σ σopen : State) (body : StmtBlock) : Type where
  kind : Contracts.ContractKind :=
    .obligation .scopeBoundaryContinuation
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace ScopeBoundarySlot

/-- Extract the supplied program-facing scope-boundary obligation evidence. -/
def get
    {Γ Γopen : TypeEnv} {σ σopen : State} {body : StmtBlock}
    (s : ScopeBoundarySlot Γ Γopen σ σopen body) : s.obligation :=
  s.evidence

end ScopeBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
