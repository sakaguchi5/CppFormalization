import CppFormalization.Cpp3.SafetyFragment.Core

/-!
# CppFormalization.Cpp3.SafetyFragment.Lifetime

Lifetime and scope-escape safety obligations.

These are C++-facing restrictions such as "do not let an inner object address
escape to a longer-lived place".  They do not say how runtime Boundary will check
addresses and they do not prove preservation across execution.
-/

namespace Cpp3
namespace SafetyFragment

/-- The opened block body does not let addresses/references to inner local
storage escape to a longer-lived context. -/
structure NoInnerAddressEscape
    (Γ Γopen : TypeEnv) (body : StmtBlock) : Type where
  kind : Contracts.ContractKind :=
    .obligation .noInnerAddressEscape
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace NoInnerAddressEscape

def get
    {Γ Γopen : TypeEnv} {body : StmtBlock}
    (h : NoInnerAddressEscape Γ Γopen body) : h.obligation :=
  h.evidence

end NoInnerAddressEscape

/-- Any address/reference used by a statement is known to outlive that use. -/
structure LifetimeOutlivesUse
    (Γ : TypeEnv) (st : CppStmt) : Type where
  effect : Effects.StmtEffect Γ st
  kind : Contracts.ContractKind :=
    .obligation .lifetimeOutlivesUse
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace LifetimeOutlivesUse

def get
    {Γ : TypeEnv} {st : CppStmt}
    (h : LifetimeOutlivesUse Γ st) : h.obligation :=
  h.evidence

end LifetimeOutlivesUse

/-- Closing a block scope does not leave an outer pointer/reference dangling. -/
structure CloseScopeNoDanglingOuterPointer
    (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Type where
  closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body
  kind : Contracts.ContractKind :=
    .obligation .closeScopeNoDanglingOuterPointer
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace CloseScopeNoDanglingOuterPointer

def get
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : CloseScopeNoDanglingOuterPointer Γ Γopen Θ Δ body) : h.obligation :=
  h.evidence

end CloseScopeNoDanglingOuterPointer

/-- Scope exit does not leak an invalid reference into the outer context. -/
structure ScopeDoesNotLeakInvalidReference
    (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Type where
  closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body
  kind : Contracts.ContractKind :=
    .obligation .scopeDoesNotLeakInvalidReference
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace ScopeDoesNotLeakInvalidReference

def get
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : ScopeDoesNotLeakInvalidReference Γ Γopen Θ Δ body) : h.obligation :=
  h.evidence

end ScopeDoesNotLeakInvalidReference

/-- A compact lifetime-safety package for a block close. -/
structure BlockCloseLifetimeSafety
    (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Type where
  noDanglingOuterPointer : CloseScopeNoDanglingOuterPointer Γ Γopen Θ Δ body
  noInvalidReferenceLeak : ScopeDoesNotLeakInvalidReference Γ Γopen Θ Δ body

end SafetyFragment
end Cpp3
