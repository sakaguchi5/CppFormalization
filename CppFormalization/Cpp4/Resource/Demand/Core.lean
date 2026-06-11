import CppFormalization.Cpp4.Core.Control
import CppFormalization.Cpp4.Resource.Capability

/-!
# CppFormalization.Cpp4.Resource.Demand.Core

Primitive resource demands and their satisfaction relation.
-/

namespace Cpp4

/-- Ambient demand context: control permissions and callable environment. -/
structure DemandContext where
  control : ControlContext
  functions : FunctionEnv

/-- Primitive resource demands. -/
inductive ResourceDemand where
  | nameBound : Ident → ResourceDemand
  | liveObject : Address → ResourceDemand
  | canRead : Address → CppType → ResourceDemand
  | canWrite : Address → CppType → ResourceDemand
  | canDerefRead : PtrValue → CppType → ResourceDemand
  | canDerefWrite : PtrValue → CppType → ResourceDemand
  | activeScope : ScopeId → ResourceDemand
  | topScope : ScopeId → ResourceDemand
  | callable : FunctionName → ResourceDemand
  | breakAllowed
  | continueAllowed
  | returnAllowed : CppType → ResourceDemand

/-- Satisfaction of a primitive resource demand. -/
def DemandSatisfied (χ : DemandContext) (σ : State) : ResourceDemand → Prop
  | .nameBound x => ∃ b, lookupBinding σ x = some b
  | .liveObject a => LiveObject σ a
  | .canRead a τ => CanRead σ a τ
  | .canWrite a τ => CanWrite σ a τ
  | .canDerefRead p τ => CanDerefRead σ p τ
  | .canDerefWrite p τ => CanDerefWrite σ p τ
  | .activeScope sid => ActiveScope σ sid
  | .topScope sid => TopScope σ sid
  | .callable f => CallableResolved χ.functions f
  | .breakAllowed => BreakAllowed χ.control
  | .continueAllowed => ContinueAllowed χ.control
  | .returnAllowed τ => ReturnAllowed χ.control τ

/-- A demand set is a finite list of primitive resource demands. -/
abbrev DemandSet := List ResourceDemand

/-- All demands in a demand set are satisfied. -/
def DemandSetSatisfied (χ : DemandContext) (σ : State) (D : DemandSet) : Prop :=
  ∀ d, d ∈ D → DemandSatisfied χ σ d

/-- Resource demand required to enter a statement.  Detailed syntax computation
lives above primitive demand and can refine this surface later. -/
structure StmtDemand where
  demands : DemandSet

/-- Resource demand required to enter a block. -/
structure BlockDemand where
  demands : DemandSet

namespace DemandSetSatisfied

theorem nil (χ : DemandContext) (σ : State) :
    DemandSetSatisfied χ σ [] := by
  intro d h
  cases h

theorem cons {χ : DemandContext} {σ : State} {d : ResourceDemand} {D : DemandSet}
    (hd : DemandSatisfied χ σ d)
    (hD : DemandSetSatisfied χ σ D) :
    DemandSetSatisfied χ σ (d :: D) := by
  intro q hq
  cases hq with
  | head => exact hd
  | tail _ htail => exact hD q htail

theorem of_cons {χ : DemandContext} {σ : State} {d : ResourceDemand} {D : DemandSet}
    (h : DemandSetSatisfied χ σ (d :: D)) :
    DemandSatisfied χ σ d ∧ DemandSetSatisfied χ σ D := by
  constructor
  · exact h d (by simp)
  · intro q hq
    exact h q (by simp [hq])

theorem append {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h₁ : DemandSetSatisfied χ σ D₁)
    (h₂ : DemandSetSatisfied χ σ D₂) :
    DemandSetSatisfied χ σ (D₁ ++ D₂) := by
  intro d hd
  cases List.mem_append.mp hd with
  | inl hleft => exact h₁ d hleft
  | inr hright => exact h₂ d hright

theorem left_of_append {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h : DemandSetSatisfied χ σ (D₁ ++ D₂)) :
    DemandSetSatisfied χ σ D₁ := by
  intro d hd
  exact h d (List.mem_append.mpr (.inl hd))

theorem right_of_append {χ : DemandContext} {σ : State} {D₁ D₂ : DemandSet}
    (h : DemandSetSatisfied χ σ (D₁ ++ D₂)) :
    DemandSetSatisfied χ σ D₂ := by
  intro d hd
  exact h d (List.mem_append.mpr (.inr hd))

end DemandSetSatisfied

end Cpp4
