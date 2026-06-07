import CppFormalization.Cpp3.Typing.Micro.Composition.ScopeBoundaryStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.OpenedBlockBodyBoundarySlot

Obligation slot for opened block-body boundaries.

The static block component opens a type scope and checks the block body there.
Runtime layers additionally need evidence that, after opening the corresponding
runtime scope, the opened block body can actually be entered.

This is not the C++ block routing rule itself.  The semantic rule

  open scope → execute opened body → close scope

belongs to Semantics.  This slot only names the programmer-facing / boundary
obligation that the opened body boundary is available in the opened runtime
state.

Close-scope lifetime safety, such as preventing dangling outer pointers after an
inner object dies, is a separate safety-fragment/stability obligation.
-/

/-- A slot for the contract needed to enter the opened block body after the
static type scope and runtime scope have both been opened. -/
structure OpenedBlockBodyBoundarySlot
    (Γ Γopen : TypeEnv) (σ σopen : State) (body : StmtBlock) : Type where
  kind : Contracts.ContractKind :=
    .obligation .openedBlockBodyBoundaryPreserved
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace OpenedBlockBodyBoundarySlot

/-- Extract the supplied program-facing opened-body-boundary obligation evidence. -/
def get
    {Γ Γopen : TypeEnv} {σ σopen : State} {body : StmtBlock}
    (s : OpenedBlockBodyBoundarySlot Γ Γopen σ σopen body) : s.obligation :=
  s.evidence

end OpenedBlockBodyBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
