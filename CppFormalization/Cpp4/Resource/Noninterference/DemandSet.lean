import CppFormalization.Cpp4.Resource.Noninterference.Core

/-!
# CppFormalization.Cpp4.Resource.Noninterference.DemandSet

List-level demand preservation.

`preserves_singleton` is useful for atom proofs, but ControlPlan transport needs
whole demand sets.  This file supplies the list combinators that let later plan,
loop, and switch proofs compose primitive noninterference facts without repeatedly
re-proving list bookkeeping.
-/

namespace Cpp4

/-- A packaged preservation certificate for a whole demand set. -/
structure PreservesDemandSet
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (D D' : DemandSet) : Type where
  preserved : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ' D'

namespace PreservesDemandSet

/-- Convert list-level preservation to the core effect-preservation boundary. -/
def toEffectPreservesDemand
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (h : PreservesDemandSet χ χ' σ σ' eff D D') :
    EffectPreservesDemand χ χ' σ σ' eff D D' := by
  constructor
  exact h.preserved

/-- Repackage an existing core preservation proof as list-level preservation. -/
def ofEffectPreservesDemand
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (h : EffectPreservesDemand χ χ' σ σ' eff D D') :
    PreservesDemandSet χ χ' σ σ' eff D D' := by
  constructor
  exact h.preserved

/-- Empty demand-set preservation. -/
def nil
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect} :
    PreservesDemandSet χ χ' σ σ' eff [] [] := by
  constructor
  intro _
  exact DemandSetSatisfied.nil χ' σ'

/-- Cons preservation: one primitive demand plus a preserved tail. -/
def cons
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {d d' : ResourceDemand} {D D' : DemandSet}
    (hd : PreservesPrimitiveDemand χ χ' σ σ' eff d d')
    (hD : PreservesDemandSet χ χ' σ σ' eff D D') :
    PreservesDemandSet χ χ' σ σ' eff (d :: D) (d' :: D') := by
  constructor
  intro h
  exact DemandSetSatisfied.cons
    (hd.preserved (h d (by simp)))
    (hD.preserved (DemandSetSatisfied.of_cons h).2)

/-- Append preservation for two independently preserved demand-set fragments. -/
def append
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {D₁ D₂ D₁' D₂' : DemandSet}
    (h₁ : PreservesDemandSet χ χ' σ σ' eff D₁ D₁')
    (h₂ : PreservesDemandSet χ χ' σ σ' eff D₂ D₂') :
    PreservesDemandSet χ χ' σ σ' eff (D₁ ++ D₂) (D₁' ++ D₂') := by
  constructor
  intro h
  exact DemandSetSatisfied.append
    (h₁.preserved (DemandSetSatisfied.left_of_append h))
    (h₂.preserved (DemandSetSatisfied.right_of_append h))

/-- Same-demand-set preservation when each member has a primitive preservation
certificate to itself. -/
def sameDemandsIfEach
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect} :
    (D : DemandSet) →
    (∀ d, d ∈ D → PreservesPrimitiveDemand χ χ' σ σ' eff d d) →
    PreservesDemandSet χ χ' σ σ' eff D D
  | [], _ => nil
  | d :: D, h =>
      cons
        (h d (by simp))
        (sameDemandsIfEach D (by
          intro q hq
          exact h q (by simp [hq])))

end PreservesDemandSet

/-- A named bridge from list preservation to core effect preservation. -/
def effectPreservesDemand_of_preservesDemandSet
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (h : PreservesDemandSet χ χ' σ σ' eff D D') :
    EffectPreservesDemand χ χ' σ σ' eff D D' :=
  h.toEffectPreservesDemand

end Cpp4
