import CppFormalization.Cpp4.Resource.Noninterference.Primitive

/-!
# CppFormalization.Cpp4.Resource.Noninterference.EffectList

C1 helpers for composing demand preservation across resource-effect lists.

The current preservation relation is intentionally semantic: the `eff` list is an
index explaining which resource effect justified the transport.  Sequential
composition therefore composes the preservation functions and records
`eff₁ ++ eff₂` as the combined effect.
-/

namespace Cpp4

namespace PreservesDemandSet

/-- Sequential composition of demand-set preservation across effect-list append. -/
def trans
    {χ₀ χ₁ χ₂ : DemandContext} {σ₀ σ₁ σ₂ : State}
    {eff₁ eff₂ : ResourceEffect} {D₀ D₁ D₂ : DemandSet}
    (h₁ : PreservesDemandSet χ₀ χ₁ σ₀ σ₁ eff₁ D₀ D₁)
    (h₂ : PreservesDemandSet χ₁ χ₂ σ₁ σ₂ eff₂ D₁ D₂) :
    PreservesDemandSet χ₀ χ₂ σ₀ σ₂ (eff₁ ++ eff₂) D₀ D₂ where
  preserved := fun hD => h₂.preserved (h₁.preserved hD)

/-- One-step demand-set preservation for an atomic resource effect. -/
abbrev atom
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffectAtom) (D D' : DemandSet) : Type :=
  PreservesDemandSet χ χ' σ σ' [eff] D D'

/-- Empty-effect preservation is just ordinary same-state demand preservation. -/
def empty
    {χ χ' : DemandContext} {σ σ' : State} {D D' : DemandSet}
    (h : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ' D') :
    PreservesDemandSet χ χ' σ σ' [] D D' where
  preserved := h

end PreservesDemandSet

end Cpp4
