import CppFormalization.Cpp3.SafetyFragment.Core

/-!
# CppFormalization.Cpp3.SafetyFragment.Deref

Dereference/read/write target safety obligations.

This layer names C++ obligations such as "the dereference target is live" and
"the target storage has the expected type".  The later Boundary layer will tie
these obligations to concrete runtime states and addresses.
-/

namespace Cpp3
namespace SafetyFragment

/-- A dereference target required by a place expression is live. -/
structure DerefTargetLive
    (Γ : TypeEnv) (p : PlaceExpr) : Type where
  effect : Effects.PlaceEffect Γ p
  kind : Contracts.ContractKind :=
    .obligation .derefTargetLive
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- A read target required by a value expression is available. -/
structure ReadableTargetAvailable
    (Γ : TypeEnv) (e : ValExpr) : Type where
  effect : Effects.ValEffect Γ e
  kind : Contracts.ContractKind :=
    .obligation .readableTargetAvailable
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- A write target required by an assignment is available. -/
structure WritableTargetAvailable
    (Γ : TypeEnv) (a : CppAssign) : Type where
  effect : Effects.AssignEffect Γ a
  kind : Contracts.ContractKind :=
    .obligation .writableTargetAvailable
  obligation : Prop
  evidence : Contracts.Requires obligation

/-- The storage used by a place has the type expected by the static surface. -/
structure TypedStorageAvailable
    (Γ : TypeEnv) (p : PlaceExpr) (τ : CppType) : Type where
  effect : Effects.PlaceEffect Γ p
  kind : Contracts.ContractKind :=
    .obligation .typedStorageAvailable
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace DerefTargetLive

def get
    {Γ : TypeEnv} {p : PlaceExpr}
    (h : DerefTargetLive Γ p) : h.obligation :=
  h.evidence

end DerefTargetLive

namespace ReadableTargetAvailable

def get
    {Γ : TypeEnv} {e : ValExpr}
    (h : ReadableTargetAvailable Γ e) : h.obligation :=
  h.evidence

end ReadableTargetAvailable

namespace WritableTargetAvailable

def get
    {Γ : TypeEnv} {a : CppAssign}
    (h : WritableTargetAvailable Γ a) : h.obligation :=
  h.evidence

end WritableTargetAvailable

namespace TypedStorageAvailable

def get
    {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType}
    (h : TypedStorageAvailable Γ p τ) : h.obligation :=
  h.evidence

end TypedStorageAvailable

/-- A value-expression dereference-safety package.

If the syntax has no dereference use, the implication is vacuous.  If it does,
the supplied obligation explains why the dereference is inside the safe C++
fragment. -/
structure ValDerefSafety
    (Γ : TypeEnv) (e : ValExpr) : Type where
  effect : Effects.ValEffect Γ e
  obligation : Prop
  evidence : Effects.ValEffect.derefUse effect → Contracts.Requires obligation

/-- A condition dereference-safety package. -/
structure CondDerefSafety
    (Γ Γc : TypeEnv) (cond : CppCond) : Type where
  effect : Effects.CondEffect Γ Γc cond
  obligation : Prop
  evidence : Effects.CondEffect.derefUse effect → Contracts.Requires obligation

/-- An initializer dereference-safety package. -/
structure InitDerefSafety
    (Γ : TypeEnv) (init : CppInit) : Type where
  effect : Effects.InitEffect Γ init
  obligation : Prop
  evidence : Effects.InitEffect.derefUse effect → Contracts.Requires obligation

end SafetyFragment
end Cpp3
