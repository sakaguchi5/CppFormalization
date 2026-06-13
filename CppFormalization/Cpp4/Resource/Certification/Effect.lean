import CppFormalization.Cpp4.Resource.Effect.All

/-!
# CppFormalization.Cpp4.Resource.Certification.Effect

Effect-generation certificates for the resource-certification pipeline.

The current `EffectTrace` is intentionally light: it exposes the resource effect
associated with an execution fragment.  This file packages that output so later
proofs can distinguish "the effect was generated" from "the effect preserves the
future demand".
-/

namespace Cpp4

/-- A machine-generated resource effect for a concrete state transition. -/
structure GeneratedEffect (σ σ' : State) : Type where
  effect : ResourceEffect
  trace : EffectTrace σ σ'
  effectEq : trace.effect = effect

namespace GeneratedEffect

/-- Generate an effect certificate from an explicit trace. -/
def ofTrace {σ σ' : State} (tr : EffectTrace σ σ') : GeneratedEffect σ σ' where
  effect := tr.effect
  trace := tr
  effectEq := rfl

/-- Build a first-pass effect certificate directly from an effect list.

This is useful before the semantics/effect-trace adequacy layer is strengthened:
`EffectTrace` currently records the resource-effect list but no additional dynamic
relation. -/
def ofEffect {σ σ' : State} (eff : ResourceEffect) : GeneratedEffect σ σ' where
  effect := eff
  trace := { effect := eff }
  effectEq := rfl

/-- The empty effect certificate. -/
def empty {σ : State} : GeneratedEffect σ σ :=
  ofEffect []

end GeneratedEffect

end Cpp4
