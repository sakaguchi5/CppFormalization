import CppFormalization.Cpp3.Typing.Micro.Composition.WhileStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.WhileBackedgeSlot

Obligation slot for while-loop backedge/reentry.

Typing can expose the condition and body channels of a `while`, but it should
not pretend that post-body runtime states automatically satisfy the condition and
body boundary again.  This slot names the later C++ contract/proof needed to
reenter the loop after a normal or continue body route.
-/

/-- A slot for the contract needed to reenter `while (cond) body` after the body
has run from `σ` to `σ₁` through a loop-reentering channel. -/
structure WhileBackedgeSlot
    (Γ : TypeEnv) (σ σ₁ : State) (cond : CppCond) (body : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .whileBackedgeInvariant
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace WhileBackedgeSlot

/-- Extract the supplied program-facing while-backedge obligation evidence. -/
def get
    {Γ : TypeEnv} {σ σ₁ : State} {cond : CppCond} {body : CppStmt}
    (s : WhileBackedgeSlot Γ σ σ₁ cond body) : s.obligation :=
  s.evidence

end WhileBackedgeSlot

end ObligationSlot
end Micro
end Typing
end Cpp3
