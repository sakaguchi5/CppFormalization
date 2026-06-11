import CppFormalization.Cpp4.Resource.Noninterference.Lifetime

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Scope

Atom-level scope transport.  Opening a scope is mostly monotone; closing a scope
requires an explicit outer-demand certificate except for direct owned-object
invalidation.
-/

namespace Cpp4

/-- Lookup is unchanged by pushing an empty scope. -/
theorem lookupBinding_pushScope
    {σ : State} {sid : ScopeId} {x : Ident} :
    lookupBinding (pushScopeState σ sid) x = lookupBinding σ x := by
  simp [pushScopeState, lookupBinding, lookupBindingFrames, emptyScopeFrame]

/-- Push-scope stable primitive demands: all existing demands except "current top
scope is sid" survive opening a fresh empty frame. -/
def PushScopeStableDemand : ResourceDemand → Prop
  | .topScope _ => False
  | _ => True

/-- Packaged preservation for an existing demand across `pushScope`.  The generic
form is a certificate because later typing will know which boundary facts are
"current top" facts and which are stable tail facts. -/
structure PushScopeExistingDemand
    (χ : DemandContext) (σ : State) (sid : ScopeId) (d : ResourceDemand) : Type where
  stable : PushScopeStableDemand d
  preserved : DemandSatisfied χ σ d → DemandSatisfied χ (pushScopeState σ sid) d

/-- Pushing an empty scope preserves an existing demand once the demand analyzer
classifies it as stable under push. -/
theorem pushScope_preserves_existing_demand
    {χ : DemandContext} {σ : State} {sid : ScopeId} {d : ResourceDemand}
    (h : PushScopeExistingDemand χ σ sid d) :
    DemandSatisfied χ σ d → DemandSatisfied χ (pushScopeState σ sid) d :=
  h.preserved

/-- An object is owned by a scope in the current runtime heap. -/
def ObjectOwnedBy (σ : State) (oid : ObjectId) (sid : ScopeId) : Prop :=
  ∃ c, σ.heap oid = some c ∧ c.lifetime.owner = sid

/-- An object is not owned by a scope in the current runtime heap. -/
def ObjectNotOwnedBy (σ : State) (oid : ObjectId) (sid : ScopeId) : Prop :=
  ∀ c, σ.heap oid = some c → c.lifetime.owner ≠ sid

/-- Closing a scope leaves heap lookup unchanged for objects not owned by it. -/
theorem heapAt_popScope_unowned
    {σ : State} {sid : ScopeId} {a : Address}
    (h : ObjectNotOwnedBy σ a.object sid) :
    heapAt (popScopeState σ sid) a = heapAt σ a := by
  unfold ObjectNotOwnedBy at h
  unfold heapAt popScopeState
  cases hcell : σ.heap a.object with
  | none => simp [hcell]
  | some c =>
      have howner : c.lifetime.owner ≠ sid := h c hcell
      simp [hcell, howner]

/-- Closing a scope invalidates read capability for an object owned by that scope. -/
theorem popScope_invalidates_owned_local_demand
    {χ : DemandContext} {σ : State} {sid : ScopeId} {a : Address} {τ : CppType}
    (howned : ObjectOwnedBy σ a.object sid) :
    ¬ DemandSatisfied χ (popScopeState σ sid) (.canRead a τ) := by
  intro hsat
  unfold DemandSatisfied at hsat
  rcases howned with ⟨c₀, hheap₀, howner₀⟩
  rcases hsat with ⟨c, v, hheap, hlive, hty, hval, hcompat⟩
  unfold heapAt popScopeState at hheap
  simp [hheap₀, howner₀] at hheap
  subst c
  unfold CellLive at hlive
  simp [endLifetimeCell] at hlive

/-- Outer-demand certificate for scope close.  Name shadowing, top-scope movement,
and owned-object invalidation are all real C++ effects, so the generic theorem is
certificate-driven at this layer. -/
structure PopScopeOuterDemand
    (χ : DemandContext) (σ : State) (sid : ScopeId) (d : ResourceDemand) : Type where
  preserved : DemandSatisfied χ σ d → DemandSatisfied χ (popScopeState σ sid) d

/-- Closing a scope preserves an outer demand once the demand analyzer proves it is
not owned by the closing frame and is not a top-frame-only fact. -/
theorem popScope_preserves_outer_demand
    {χ : DemandContext} {σ : State} {sid : ScopeId} {d : ResourceDemand}
    (h : PopScopeOuterDemand χ σ sid d) :
    DemandSatisfied χ σ d → DemandSatisfied χ (popScopeState σ sid) d :=
  h.preserved

end Cpp4
