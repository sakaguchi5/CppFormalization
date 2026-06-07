import CppFormalization.Cpp3.Typing.Micro.Composition.WhileStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.LoopBackedgeBoundarySlot

Obligation slot for while-loop backedge boundary preservation.

Typing exposes the condition and body channels of a `while`, but it should not
pretend that post-body runtime states automatically satisfy the next condition
or loop-body boundary again.

The C++ semantic routing rule

  body normal/continue → re-evaluate condition

belongs to Semantics.  This slot only names the practical C++ obligation that
the body route does not destroy the boundary needed at the loop backedge.

In more concrete C++ terms, this rules out cases such as:

  while (*p < 10) {
    p = nullptr;
  }

unless additional evidence explains why the next guard evaluation is still safe.
-/

/-- A slot for the contract needed to reenter `while (cond) body` after the body
has run from `σ` to `σ₁` through a loop-reentering channel.

This does not assert termination.  It only records that the backedge boundary is
preserved well enough for the next condition/body boundary to be reconstructed.
-/
structure LoopBackedgeBoundarySlot
    (Γ : TypeEnv) (σ σ₁ : State) (cond : CppCond) (body : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .loopBodyPreservesBackedgeBoundary
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace LoopBackedgeBoundarySlot

/-- Extract the supplied program-facing while-backedge-boundary obligation evidence. -/
def get
    {Γ : TypeEnv} {σ σ₁ : State} {cond : CppCond} {body : CppStmt}
    (s : LoopBackedgeBoundarySlot Γ σ σ₁ cond body) : s.obligation :=
  s.evidence

end LoopBackedgeBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
