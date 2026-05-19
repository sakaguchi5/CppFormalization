import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Typing.ControlProfile
import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Closure.Internal.SeqClosureRouteCI

namespace Cpp


/-!
## Seq decomposition extracted

The seq scaffold/route/stability/closure shell previously accumulated
in this file now lives in:
* `SeqScaffoldRouteCI`
* `SeqTailStabilityRouteCI`
* `SeqClosureRouteCI`
-/

/-!
## Ite branch boundary extraction

Unlike `seq`, `ite` does not enter a tail through a post-state/post-environment
computed by the head statement.  Both branches are entered from the original
state and environment.  Therefore structural and dynamic branch boundaries are
theorem-backed projections from the whole `ite` boundary; the remaining debt is
branch static and branch adequacy.
-/

/-- Condition readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_cond
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | ite _ hcond _ _ =>
      exact hcond

/-- Then-branch readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_then
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | ite _ _ hthen _ =>
      exact hthen

/-- Else-branch readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_else
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | ite _ _ _ helse =>
      exact helse

/--
Then-branch structural boundary projected from the whole `ite` boundary.

This is theorem-backed because `WellFormedStmt`, `BreakWellScoped`, and
`ContinueWellScoped` all decompose structurally over `ite`.
-/
theorem ite_then_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/--
Else-branch structural boundary projected from the whole `ite` boundary.

This is theorem-backed because `WellFormedStmt`, `BreakWellScoped`, and
`ContinueWellScoped` all decompose structurally over `ite`.
-/
theorem ite_else_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStructuralBoundary Γ t := by
  have hwf : WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

/--
Dynamic boundary for the then branch of an `ite`.

The branch starts in the same state as the whole `ite`; the branch readiness is
a direct projection of `StmtReadyConcrete.ite`.
-/
def ite_then_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := ite_ready_then hentry.dynamic.safe }

/--
Dynamic boundary for the else branch of an `ite`.

The branch starts in the same state as the whole `ite`; the branch readiness is
a direct projection of `StmtReadyConcrete.ite`.
-/
def ite_else_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyDynamicBoundary Γ σ t :=
  { state := hentry.dynamic.state
    safe := ite_ready_else hentry.dynamic.safe }

/--
Type-level root payload for a selected branch profile.

This is the small piece of data needed to define the branch root and its
coherence proof without keeping root/coherence as an axiom field.
-/
inductive IteBranchRootPayloadCI
    {Γ : TypeEnv} {st : CppStmt}
    (profile : BodyControlProfile Γ st) : Type where
  | normal
      {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}}
      (hprofile : profile.summary.normalOut = some out) :
      IteBranchRootPayloadCI profile
  | returned
      {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}}
      (hprofile : profile.summary.returnOut = some out) :
      IteBranchRootPayloadCI profile

namespace IteBranchRootPayloadCI

/-- The branch entry witness determined by a root payload. -/
def toRoot
    {Γ : TypeEnv} {st : CppStmt}
    {profile : BodyControlProfile Γ st}
    (p : IteBranchRootPayloadCI profile) :
    BodyEntryWitness Γ st :=
  match p with
  | .normal (out := out) _ => .normal out
  | .returned (out := out) _ => .returned out

/-- Root coherence is definitionally induced by the root payload. -/
theorem toRootCoherent
    {Γ : TypeEnv} {st : CppStmt}
    {profile : BodyControlProfile Γ st}
    (p : IteBranchRootPayloadCI profile) :
    BodyRootCoherent profile p.toRoot := by
  cases p with
  | normal hprofile =>
      exact BodyRootCoherent.normal hprofile
  | returned hprofile =>
      exact BodyRootCoherent.returned hprofile

end IteBranchRootPayloadCI

/--
A Type-level normal slot for an extracted `ite` branch profile.
-/
structure IteBranchNormalSlotCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  Δ : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Δ

namespace IteBranchNormalSlotCI

def out
    {Γ : TypeEnv} {st : CppStmt}
    (n : IteBranchNormalSlotCI Γ st) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} :=
  ⟨n.Δ, n.hty⟩

end IteBranchNormalSlotCI

/--
A Type-level return slot for an extracted `ite` branch profile.
-/
structure IteBranchReturnSlotCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  Δ : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Δ

namespace IteBranchReturnSlotCI

def out
    {Γ : TypeEnv} {st : CppStmt}
    (r : IteBranchReturnSlotCI Γ st) :
    {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} :=
  ⟨r.Δ, r.hty⟩

end IteBranchReturnSlotCI

/--
Slot-level profile payload for one branch of an `ite`.

A branch profile is just an optional normal slot and an optional return slot.
The root is not an independent field: it is chosen from one of the selected
slots, and the old root/coherence payload is derived by definition below.
-/
structure IteBranchProfileSlotPayloadCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  normalSlot : Option (IteBranchNormalSlotCI Γ st)
  returnSlot : Option (IteBranchReturnSlotCI Γ st)
  rootChoice :
    Sum
      ({ n : IteBranchNormalSlotCI Γ st // normalSlot = some n })
      ({ r : IteBranchReturnSlotCI Γ st // returnSlot = some r })

namespace IteBranchProfileSlotPayloadCI

/-- Convert selected branch slots into the actual branch control profile. -/
def toProfile
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    BodyControlProfile Γ st :=
  { summary :=
      { normalOut := S.normalSlot.map (fun n => IteBranchNormalSlotCI.out n)
        returnOut := S.returnSlot.map (fun r => IteBranchReturnSlotCI.out r) } }

/--
The root payload induced by the selected root slot.

This is the branch analogue of the seq slot-to-profile bridge: once the branch
slots and root choice are selected, root/coherence is definitional.
-/
def toRootPayload
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    IteBranchRootPayloadCI S.toProfile := by
  cases S.rootChoice with
  | inl hn =>
      rcases hn with ⟨n, hn⟩
      exact
        IteBranchRootPayloadCI.normal
          (out := IteBranchNormalSlotCI.out n)
          (by simp [toProfile, hn, IteBranchNormalSlotCI.out])
  | inr hr =>
      rcases hr with ⟨r, hr⟩
      exact
        IteBranchRootPayloadCI.returned
          (out := IteBranchReturnSlotCI.out r)
          (by simp [toProfile, hr, IteBranchReturnSlotCI.out])

end IteBranchProfileSlotPayloadCI

/--
Profile payload for one branch of an `ite`.

The remaining static choice is now explicit: choose a branch profile, and choose
one available root payload for that profile.  The root witness and coherence
record are derived from this payload by definitions below.
-/
structure IteBranchProfilePayloadCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  profile : BodyControlProfile Γ st
  rootPayload : IteBranchRootPayloadCI profile

namespace IteBranchProfilePayloadCI

/-- Build the old profile payload shape from the canonical slot-level payload. -/
def ofSlotPayload
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    IteBranchProfilePayloadCI Γ st :=
  { profile := S.toProfile
    rootPayload := S.toRootPayload }

end IteBranchProfilePayloadCI

/--
Root/coherence scaffold for a chosen branch profile.

This structure is kept as a readable compatibility package, but it is produced
by `def` from `IteBranchProfilePayloadCI`; it is not an independent axiom.
-/
structure IteBranchRootScaffoldCI
    (Γ : TypeEnv) (st : CppStmt)
    (profile : BodyControlProfile Γ st) : Type where
  root : BodyEntryWitness Γ st
  rootCoherent : BodyRootCoherent profile root

namespace IteBranchRootScaffoldCI

/-- Build branch root/coherence from the selected profile payload. -/
def ofProfilePayload
    {Γ : TypeEnv} {st : CppStmt}
    (P : IteBranchProfilePayloadCI Γ st) :
    IteBranchRootScaffoldCI Γ st P.profile :=
  { root := P.rootPayload.toRoot
    rootCoherent := P.rootPayload.toRootCoherent }

end IteBranchRootScaffoldCI

/--
Static scaffold for one branch of an `ite`, excluding the coarse `typed0`
payload.

The `typed0` field is theorem-backed from the whole `ite` typing below.  The
only primitive remaining static debt is the profile payload.  Root/coherence is
assembled by definition from that payload.
-/
structure IteBranchStaticScaffoldCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  profilePayload : IteBranchProfilePayloadCI Γ st

namespace IteBranchStaticScaffoldCI

/-- The selected branch profile. -/
def profile
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st) :
    BodyControlProfile Γ st :=
  h.profilePayload.profile

/-- The branch root/coherence scaffold induced by the selected profile payload. -/
def rootScaffold
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st) :
    IteBranchRootScaffoldCI Γ st h.profile :=
  IteBranchRootScaffoldCI.ofProfilePayload h.profilePayload

/-- Assemble a branch static boundary from theorem-backed `typed0`. -/
def toBodyStaticBoundaryCI
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st)
    (htyped : WellTypedFrom Γ st) :
    BodyStaticBoundaryCI Γ st :=
  { typed0 := htyped
    profile := h.profile
    root := h.rootScaffold.root
    rootCoherent := h.rootScaffold.rootCoherent }

end IteBranchStaticScaffoldCI

/--
The then branch of a well-typed `ite` is well typed.

This is theorem-backed from the coarse `typed0` payload of the whole `ite`.
-/
theorem ite_then_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    WellTypedFrom Γ s := by
  rcases hentry.static.typed0 with ⟨Δ, htyIte⟩
  cases htyIte with
  | ite _ hthen _ =>
      exact ⟨_, hthen⟩

/--
The else branch of a well-typed `ite` is well typed.

This is theorem-backed from the coarse `typed0` payload of the whole `ite`.
-/
theorem ite_else_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    WellTypedFrom Γ t := by
  rcases hentry.static.typed0 with ⟨Δ, htyIte⟩
  cases htyIte with
  | ite _ _ helse =>
      exact ⟨_, helse⟩

/--
Remaining then-branch slot-level profile payload obligation.

This is narrower than selecting an arbitrary branch profile: the profile is now
assembled from explicit normal/return slots, and the root is chosen from those
selected slots.
-/
axiom ite_then_profile_slot_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfileSlotPayloadCI Γ s

/--
Remaining else-branch slot-level profile payload obligation.

This is narrower than selecting an arbitrary branch profile: the profile is now
assembled from explicit normal/return slots, and the root is chosen from those
selected slots.
-/
axiom ite_else_profile_slot_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfileSlotPayloadCI Γ t

/-- Compatibility profile payload for the then branch. -/
noncomputable def ite_then_profile_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfilePayloadCI Γ s :=
  IteBranchProfilePayloadCI.ofSlotPayload
    (ite_then_profile_slot_payload_ci_of_entry hentry)

/-- Compatibility profile payload for the else branch. -/
noncomputable def ite_else_profile_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfilePayloadCI Γ t :=
  IteBranchProfilePayloadCI.ofSlotPayload
    (ite_else_profile_slot_payload_ci_of_entry hentry)

/-- Then-branch root/coherence scaffold induced by the selected profile payload. -/
noncomputable def ite_then_root_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchRootScaffoldCI Γ s
      (ite_then_profile_payload_ci_of_entry hentry).profile :=
  IteBranchRootScaffoldCI.ofProfilePayload
    (ite_then_profile_payload_ci_of_entry hentry)

/-- Else-branch root/coherence scaffold induced by the selected profile payload. -/
noncomputable def ite_else_root_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchRootScaffoldCI Γ t
      (ite_else_profile_payload_ci_of_entry hentry).profile :=
  IteBranchRootScaffoldCI.ofProfilePayload
    (ite_else_profile_payload_ci_of_entry hentry)

/-- Compatibility static scaffold for the then branch. -/
noncomputable def ite_then_static_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticScaffoldCI Γ s :=
  { profilePayload := ite_then_profile_payload_ci_of_entry hentry }

/-- Compatibility static scaffold for the else branch. -/
noncomputable def ite_else_static_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticScaffoldCI Γ t :=
  { profilePayload := ite_else_profile_payload_ci_of_entry hentry }

/-- Then-branch static boundary assembled from scaffold plus theorem-backed typing. -/
noncomputable def ite_then_static_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStaticBoundaryCI Γ s :=
  (ite_then_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (ite_then_typed0_of_entry hentry)

/-- Else-branch static boundary assembled from scaffold plus theorem-backed typing. -/
noncomputable def ite_else_static_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStaticBoundaryCI Γ t :=
  (ite_else_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (ite_else_typed0_of_entry hentry)

/--
Runtime decision for an actual branch-normal execution of an `ite` branch.

This is the branch analogue of the seq left-return runtime decision: an actual
branch execution must be reflected by the selected normal channel in the branch
profile.
-/
structure IteBranchNormalRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st)
    {σ' : State}
    (_hstep : BigStepStmt σ st .normal σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Delta
  hprofile : P.summary.normalOut = some ⟨Delta, hty⟩

namespace IteBranchNormalRuntimeDecisionCI

/-- Forget the runtime normal decision to ordinary adequacy evidence. -/
def toExists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (d : IteBranchNormalRuntimeDecisionCI Γ σ st P hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      P.summary.normalOut = some out :=
  ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩

end IteBranchNormalRuntimeDecisionCI

/--
Runtime decision for an actual branch-return execution of an `ite` branch.

An actual branch return must be reflected by the selected return channel in the
branch profile.
-/
structure IteBranchReturnRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st)
    {rv : Option Value} {σ' : State}
    (_hstep : BigStepStmt σ st (.returnResult rv) σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Delta
  hprofile : P.summary.returnOut = some ⟨Delta, hty⟩

namespace IteBranchReturnRuntimeDecisionCI

/-- Forget the runtime return decision to ordinary adequacy evidence. -/
def toExists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ st (.returnResult rv) σ'}
    (d : IteBranchReturnRuntimeDecisionCI Γ σ st P hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      P.summary.returnOut = some out :=
  ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩

end IteBranchReturnRuntimeDecisionCI

/--
Slot-aware runtime decision for an actual branch-normal execution.

The decision records that the runtime normal typing witness is exactly the
selected normal slot of the branch profile payload, not merely that the induced
profile contains an equal normal output.
-/
structure IteBranchNormalSlotRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {σ' : State}
    (_hstep : BigStepStmt σ st .normal σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Delta
  hslot : S.normalSlot = some ⟨Delta, hty⟩

namespace IteBranchNormalSlotRuntimeDecisionCI

/-- Forget the slot-aware runtime decision to the profile-level decision. -/
def toRuntimeDecision
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (d : IteBranchNormalSlotRuntimeDecisionCI Γ σ st S hstep) :
    IteBranchNormalRuntimeDecisionCI Γ σ st S.toProfile hstep :=
  { Delta := d.Delta
    hty := d.hty
    hprofile := by
      simp [IteBranchProfileSlotPayloadCI.toProfile, d.hslot,
        IteBranchNormalSlotCI.out] }

end IteBranchNormalSlotRuntimeDecisionCI

/--
Slot-aware runtime decision for an actual branch-return execution.

The decision records that the runtime return typing witness is exactly the
selected return slot of the branch profile payload.
-/
structure IteBranchReturnSlotRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {rv : Option Value} {σ' : State}
    (_hstep : BigStepStmt σ st (.returnResult rv) σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Delta
  hslot : S.returnSlot = some ⟨Delta, hty⟩

namespace IteBranchReturnSlotRuntimeDecisionCI

/-- Forget the slot-aware runtime decision to the profile-level decision. -/
def toRuntimeDecision
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ st (.returnResult rv) σ'}
    (d : IteBranchReturnSlotRuntimeDecisionCI Γ σ st S hstep) :
    IteBranchReturnRuntimeDecisionCI Γ σ st S.toProfile hstep :=
  { Delta := d.Delta
    hty := d.hty
    hprofile := by
      simp [IteBranchProfileSlotPayloadCI.toProfile, d.hslot,
        IteBranchReturnSlotCI.out] }

end IteBranchReturnSlotRuntimeDecisionCI

/--
Runtime-decision adequacy support for one `ite` branch.

This keeps the branch adequacy obligation aligned with the selected branch
profile instead of exposing only ordinary `BodyAdequacyCI` evidence.
-/
structure IteBranchAdequacySupportCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  normalDecision :
    ∀ {σ' : State}
      (hstep : BigStepStmt σ st .normal σ'),
      IteBranchNormalRuntimeDecisionCI Γ σ st P hstep
  returnDecision :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ st (.returnResult rv) σ'),
      IteBranchReturnRuntimeDecisionCI Γ σ st P hstep

namespace IteBranchAdequacySupportCI

/-- Forget runtime-decision support to ordinary `BodyAdequacyCI`. -/
def toBodyAdequacyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : IteBranchAdequacySupportCI Γ σ st P) :
    BodyAdequacyCI Γ σ st P :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ' hstep
      let d := A.normalDecision hstep
      exact ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩)
    (returnWitness := by
      intro rv σ' hstep
      let d := A.returnDecision hstep
      exact ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩)

end IteBranchAdequacySupportCI

/--
Slot-aware runtime-decision adequacy support for one `ite` branch.

This is the canonical branch adequacy obligation: actual normal/return branch
executions must use the selected normal/return slots of the branch profile
payload.
-/
structure IteBranchSlotAdequacySupportCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st) : Type where
  normalDecision :
    ∀ {σ' : State}
      (hstep : BigStepStmt σ st .normal σ'),
      IteBranchNormalSlotRuntimeDecisionCI Γ σ st S hstep
  returnDecision :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ st (.returnResult rv) σ'),
      IteBranchReturnSlotRuntimeDecisionCI Γ σ st S hstep

namespace IteBranchSlotAdequacySupportCI

/-- Forget slot-aware adequacy support to profile-level adequacy support. -/
def toAdequacySupport
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    (A : IteBranchSlotAdequacySupportCI Γ σ st S) :
    IteBranchAdequacySupportCI Γ σ st S.toProfile :=
  { normalDecision := by
      intro σ' hstep
      exact (A.normalDecision hstep).toRuntimeDecision
    returnDecision := by
      intro rv σ' hstep
      exact (A.returnDecision hstep).toRuntimeDecision }

end IteBranchSlotAdequacySupportCI

namespace IteBranchProfileSlotPayloadCI

/--
Type-level inversion of a normal summary equality for a slot-generated branch
profile.

This is purely structural `Option.map` inversion; it is not a semantic adequacy
theorem.
-/
def normalSlotWitness_of_toProfile_normalOut_eq_some
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}}
    (h : S.toProfile.summary.normalOut = some out) :
    { n : IteBranchNormalSlotCI Γ st //
      S.normalSlot = some n ∧ IteBranchNormalSlotCI.out n = out } := by
  cases hslot : S.normalSlot with
  | none =>
      simp [IteBranchProfileSlotPayloadCI.toProfile, hslot] at h
  | some n =>
      refine ⟨n, ?_⟩
      constructor
      · rfl
      · simpa [IteBranchProfileSlotPayloadCI.toProfile, hslot] using h

/--
Invert a normal summary equality for a slot-generated branch profile.

This is the proof-only projection of
`normalSlotWitness_of_toProfile_normalOut_eq_some`.
-/
theorem normalSlot_of_toProfile_normalOut_eq_some
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}}
    (h : S.toProfile.summary.normalOut = some out) :
    ∃ n : IteBranchNormalSlotCI Γ st,
      S.normalSlot = some n ∧ IteBranchNormalSlotCI.out n = out := by
  let w := S.normalSlotWitness_of_toProfile_normalOut_eq_some h
  exact ⟨w.val, w.property⟩

/--
Type-level inversion of a return summary equality for a slot-generated branch
profile.
-/
def returnSlotWitness_of_toProfile_returnOut_eq_some
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}}
    (h : S.toProfile.summary.returnOut = some out) :
    { r : IteBranchReturnSlotCI Γ st //
      S.returnSlot = some r ∧ IteBranchReturnSlotCI.out r = out } := by
  cases hslot : S.returnSlot with
  | none =>
      simp [IteBranchProfileSlotPayloadCI.toProfile, hslot] at h
  | some r =>
      refine ⟨r, ?_⟩
      constructor
      · rfl
      · simpa [IteBranchProfileSlotPayloadCI.toProfile, hslot] using h

/--
Invert a return summary equality for a slot-generated branch profile.

This is the proof-only projection of
`returnSlotWitness_of_toProfile_returnOut_eq_some`.
-/
theorem returnSlot_of_toProfile_returnOut_eq_some
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}}
    (h : S.toProfile.summary.returnOut = some out) :
    ∃ r : IteBranchReturnSlotCI Γ st,
      S.returnSlot = some r ∧ IteBranchReturnSlotCI.out r = out := by
  let w := S.returnSlotWitness_of_toProfile_returnOut_eq_some h
  exact ⟨w.val, w.property⟩

end IteBranchProfileSlotPayloadCI

namespace IteBranchSlotAdequacySupportCI

/--
Convert branch-local `BodyAdequacyCI` for `S.toProfile` into slot-aware
adequacy support for `S`.

The adequacy provider supplies the normal/return profile witness directly, and
the slot payload inverts it into the corresponding selected slot.
-/
def ofBodyAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    (A : BodyAdequacyCI Γ σ st S.toProfile) :
    IteBranchSlotAdequacySupportCI Γ σ st S :=
  { normalDecision := by
      intro σ' hstep
      let hout := A.normalWitness hstep
      let w := S.normalSlotWitness_of_toProfile_normalOut_eq_some hout.property
      exact
        { Delta := w.val.Δ
          hty := w.val.hty
          hslot := w.property.1 }
    returnDecision := by
      intro rv σ' hstep
      let hout := A.returnWitness hstep
      let w := S.returnSlotWitness_of_toProfile_returnOut_eq_some hout.property
      exact
        { Delta := w.val.Δ
          hty := w.val.hty
          hslot := w.property.1 } }

/--
Convert witness-producing branch-local adequacy for `S.toProfile` into
slot-aware adequacy support for `S`.

Unlike `ofBodyAdequacy`, this route does not need to choose the profile output
from a `Prop`-level existential; the profile witness is supplied directly by the
witness-producing adequacy layer.
-/
def ofBodyAdequacyWitness
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st)
    (A : BodyAdequacyCI Γ σ st S.toProfile) :
    IteBranchSlotAdequacySupportCI Γ σ st S :=
  { normalDecision := by
      intro σ' hstep
      let hout := A.normalWitness hstep
      let w := S.normalSlotWitness_of_toProfile_normalOut_eq_some hout.property
      exact
        { Delta := w.val.Δ
          hty := w.val.hty
          hslot := w.property.1 }
    returnDecision := by
      intro rv σ' hstep
      let hout := A.returnWitness hstep
      let w := S.returnSlotWitness_of_toProfile_returnOut_eq_some hout.property
      exact
        { Delta := w.val.Δ
          hty := w.val.hty
          hslot := w.property.1 } }

end IteBranchSlotAdequacySupportCI

/--
Remaining then-branch witness-producing adequacy obligation.

This replaces the two channel-specific then-branch runtime-decision axioms.
The branch-local adequacy provider is indexed by the selected then-branch slot
payload profile, so the normal/return channel decisions are derived uniformly
from one branch adequacy package.
-/
axiom ite_then_body_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ s
      (ite_then_profile_slot_payload_ci_of_entry hentry).toProfile

/--
Remaining else-branch witness-producing adequacy obligation.

This replaces the two channel-specific else-branch runtime-decision axioms.
-/
axiom ite_else_body_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ t
      (ite_else_profile_slot_payload_ci_of_entry hentry).toProfile

/--
Compatibility package for then-branch slot-aware adequacy support.
The primitive obligation is now one witness-producing branch-local adequacy
provider, not two separate runtime-decision axioms.
-/
noncomputable def ite_then_slot_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchSlotAdequacySupportCI Γ σ s
      (ite_then_profile_slot_payload_ci_of_entry hentry) :=
  IteBranchSlotAdequacySupportCI.ofBodyAdequacy
    (ite_then_profile_slot_payload_ci_of_entry hentry)
    (ite_then_body_adequacy_ci_of_entry hentry)

/--
Compatibility package for else-branch slot-aware adequacy support.
-/
noncomputable def ite_else_slot_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchSlotAdequacySupportCI Γ σ t
      (ite_else_profile_slot_payload_ci_of_entry hentry) :=
  IteBranchSlotAdequacySupportCI.ofBodyAdequacy
    (ite_else_profile_slot_payload_ci_of_entry hentry)
    (ite_else_body_adequacy_ci_of_entry hentry)

/--
Compatibility name for the old then normal runtime-decision surface.
This is now a definition derived from the then witness-producing adequacy
provider, not a primitive axiom.
-/
noncomputable def ite_then_normal_slot_runtime_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ∀ {σ' : State} (hstep : BigStepStmt σ s .normal σ'),
      IteBranchNormalSlotRuntimeDecisionCI Γ σ s
        (ite_then_profile_slot_payload_ci_of_entry hentry) hstep :=
  (ite_then_slot_adequacy_support_ci_of_entry hentry).normalDecision

/--
Compatibility name for the old then return runtime-decision surface.
This is now derived from the then witness-producing adequacy provider.
-/
noncomputable def ite_then_return_slot_runtime_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ s (.returnResult rv) σ'),
      IteBranchReturnSlotRuntimeDecisionCI Γ σ s
        (ite_then_profile_slot_payload_ci_of_entry hentry) hstep :=
  (ite_then_slot_adequacy_support_ci_of_entry hentry).returnDecision

/--
Compatibility name for the old else normal runtime-decision surface.
This is now derived from the else witness-producing adequacy provider.
-/
noncomputable def ite_else_normal_slot_runtime_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ∀ {σ' : State} (hstep : BigStepStmt σ t .normal σ'),
      IteBranchNormalSlotRuntimeDecisionCI Γ σ t
        (ite_else_profile_slot_payload_ci_of_entry hentry) hstep :=
  (ite_else_slot_adequacy_support_ci_of_entry hentry).normalDecision

/--
Compatibility name for the old else return runtime-decision surface.
This is now derived from the else witness-producing adequacy provider.
-/
noncomputable def ite_else_return_slot_runtime_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ t (.returnResult rv) σ'),
      IteBranchReturnSlotRuntimeDecisionCI Γ σ t
        (ite_else_profile_slot_payload_ci_of_entry hentry) hstep :=
  (ite_else_slot_adequacy_support_ci_of_entry hentry).returnDecision

/-- Compatibility profile-level adequacy support for the then branch. -/
noncomputable def ite_then_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchAdequacySupportCI Γ σ s (ite_then_static_ci_of_entry hentry).profile := by
  simpa [ite_then_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_then_static_scaffold_ci_of_entry,
    ite_then_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_then_slot_adequacy_support_ci_of_entry hentry).toAdequacySupport

/-- Compatibility profile-level adequacy support for the else branch. -/
noncomputable def ite_else_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchAdequacySupportCI Γ σ t (ite_else_static_ci_of_entry hentry).profile := by
  simpa [ite_else_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_else_static_scaffold_ci_of_entry,
    ite_else_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_else_slot_adequacy_support_ci_of_entry hentry).toAdequacySupport

/-- Compatibility adequacy wrapper for the then branch. -/
noncomputable def ite_then_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ s (ite_then_static_ci_of_entry hentry).profile :=
  (ite_then_adequacy_support_ci_of_entry hentry).toBodyAdequacyCI

/-- Compatibility adequacy wrapper for the else branch. -/
noncomputable def ite_else_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ t (ite_else_static_ci_of_entry hentry).profile :=
  (ite_else_adequacy_support_ci_of_entry hentry).toBodyAdequacyCI

/--
Static+adequacy package for one branch of an `ite`.

Compatibility package assembled from the separated static scaffold and adequacy
obligations.  It is no longer a primitive axiom.
-/
structure IteBranchStaticAdequacyCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

/--
Witness-producing static+adequacy package for one branch of an `ite`.

This is the provider-facing analogue of `IteBranchStaticAdequacyCI`.  The
ordinary proof-only package remains available by forgetting the witness
provider.
-/
structure IteBranchStaticAdequacyProviderCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ st
  adequacyWitness : BodyAdequacyCI Γ σ st static.profile

namespace IteBranchStaticAdequacyProviderCI

/-- Forget the witness-producing branch package to the older proof-only API. -/
def toStaticAdequacyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (B : IteBranchStaticAdequacyProviderCI Γ σ st) :
    IteBranchStaticAdequacyCI Γ σ st :=
  { static := B.static
    adequacy := B.adequacyWitness }

end IteBranchStaticAdequacyProviderCI

/--
Then-branch witness adequacy transported to the actual static boundary profile.
-/
noncomputable def ite_then_body_adequacy_ci_of_static_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ s (ite_then_static_ci_of_entry hentry).profile := by
  simpa [ite_then_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_then_static_scaffold_ci_of_entry,
    ite_then_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_then_body_adequacy_ci_of_entry hentry)

/--
Else-branch witness adequacy transported to the actual static boundary profile.
-/
noncomputable def ite_else_body_adequacy_ci_of_static_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ t (ite_else_static_ci_of_entry hentry).profile := by
  simpa [ite_else_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_else_static_scaffold_ci_of_entry,
    ite_else_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_else_body_adequacy_ci_of_entry hentry)

/-- Witness-producing compatibility package for the then branch. -/
noncomputable def ite_then_static_adequacy_provider_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyProviderCI Γ σ s :=
  { static := ite_then_static_ci_of_entry hentry
    adequacyWitness := ite_then_body_adequacy_ci_of_static_entry hentry }

/-- Witness-producing compatibility package for the else branch. -/
noncomputable def ite_else_static_adequacy_provider_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyProviderCI Γ σ t :=
  { static := ite_else_static_ci_of_entry hentry
    adequacyWitness := ite_else_body_adequacy_ci_of_static_entry hentry }

/-- Compatibility package for the then branch. -/
noncomputable def ite_then_static_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyCI Γ σ s :=
  (ite_then_static_adequacy_provider_ci_of_entry hentry).toStaticAdequacyCI

/-- Compatibility package for the else branch. -/
noncomputable def ite_else_static_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyCI Γ σ t :=
  (ite_else_static_adequacy_provider_ci_of_entry hentry).toStaticAdequacyCI

/--
Branch closure boundaries for an `ite`.

Compatibility package assembled from theorem-backed structural/dynamic
projections and the remaining static+adequacy branch obligations.
-/
structure IteBranchClosureBoundariesCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) : Type where
  thenBoundary : BodyClosureBoundaryCI Γ σ s
  elseBoundary : BodyClosureBoundaryCI Γ σ t

/--
Compatibility constructor for old callers.

The real remaining obligations are now the two static+adequacy branch packages;
the structural and dynamic pieces are theorem-backed.
-/
noncomputable def ite_branch_closure_boundaries_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchClosureBoundariesCI hentry := by
  let hthen := ite_then_static_adequacy_ci_of_entry hentry
  let helse := ite_else_static_adequacy_ci_of_entry hentry
  exact
    { thenBoundary :=
        mkBodyClosureBoundaryCI
          (ite_then_structural_boundary_of_entry hentry)
          hthen.static
          (ite_then_dynamic_boundary_of_entry hentry)
          hthen.adequacy
      elseBoundary :=
        mkBodyClosureBoundaryCI
          (ite_else_structural_boundary_of_entry hentry)
          helse.static
          (ite_else_dynamic_boundary_of_entry hentry)
          helse.adequacy }

/-- Extract condition readiness from a concrete-ready `ite`. -/
theorem ite_condition_ready_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ExprReadyConcrete Γ σ c (.base .bool) := by
  cases hentry.dynamic.safe with
  | ite _ hcond _ _ =>
      exact hcond

/-- Operational result assembly for the true branch of an `ite`. -/
theorem ite_function_body_result_true
    {σ : State} {c : ValExpr} {s t : CppStmt}
    (hcond : BigStepValue σ c (.bool true))
    (hthen : FunctionBodyClosureResult σ s) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  rcases hthen with hthenTerm | hthenDiv
  · rcases hthenTerm with ⟨ex, σ', hbody⟩
    cases hbody with
    | fallthrough hstep =>
        exact Or.inl ⟨.fellThrough, σ', BigStepFunctionBody.fallthrough
          (BigStepStmt.iteTrue hcond hstep)⟩
    | returning hstep =>
        rename_i rv
        exact Or.inl ⟨.returned rv, σ', BigStepFunctionBody.returning
          (BigStepStmt.iteTrue hcond hstep)⟩
  · exact Or.inr (BigStepStmtDiv.iteTrue hcond hthenDiv)

/-- Operational result assembly for the false branch of an `ite`. -/
theorem ite_function_body_result_false
    {σ : State} {c : ValExpr} {s t : CppStmt}
    (hcond : BigStepValue σ c (.bool false))
    (helse : FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  rcases helse with helseTerm | helseDiv
  · rcases helseTerm with ⟨ex, σ', hbody⟩
    cases hbody with
    | fallthrough hstep =>
        exact Or.inl ⟨.fellThrough, σ', BigStepFunctionBody.fallthrough
          (BigStepStmt.iteFalse hcond hstep)⟩
    | returning hstep =>
        rename_i rv
        exact Or.inl ⟨.returned rv, σ', BigStepFunctionBody.returning
          (BigStepStmt.iteFalse hcond hstep)⟩
  · exact Or.inr (BigStepStmtDiv.iteFalse hcond helseDiv)

/--
Theorem-backed `ite` closure shell.

The only abstract input is branch-boundary extraction. Once the condition is
ready, expression readiness supplies a boolean evaluation; the corresponding
branch closure is then lifted to the whole conditional by the operational
assembly lemmas above.
-/
theorem ite_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t))
    (thenClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyClosureBoundaryCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  let hb := ite_branch_closure_boundaries_ci_of_entry hentry
  have hcondReady : ExprReadyConcrete Γ σ c (.base .bool) :=
    ite_condition_ready_of_entry hentry
  rcases expr_ready_to_bigstep hcondReady with ⟨v, hcondEval⟩
  have hcompat : ValueCompat v (.base .bool) :=
    expr_ready_eval_compat hcondReady hcondEval
  cases hcompat with
  | bool =>
      rename_i b
      cases b with
      | false =>
          exact ite_function_body_result_false hcondEval
            (elseClosure hb.elseBoundary)
      | true =>
          exact ite_function_body_result_true hcondEval
            (thenClosure hb.thenBoundary)

theorem ite_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.ite c s t))
    (thenClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyReadyCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  exact
    ite_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hthenBoundary => thenClosure hthenBoundary.toBodyReadyCI)
      (fun helseBoundary => elseClosure helseBoundary.toBodyReadyCI)

end Cpp
