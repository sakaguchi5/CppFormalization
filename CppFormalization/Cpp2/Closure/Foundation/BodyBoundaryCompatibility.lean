import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

axiom heapInitializedValuesTyped_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    heapInitializedValuesTyped σ
--補題
private theorem frame_eq_of_scope_lookup
    {σ : State} {k : Nat} {fr₁ fr₂ : ScopeFrame}
    (h₁ : σ.scopes[k]? = some fr₁)
    (h₂ : σ.scopes[k]? = some fr₂) :
    fr₁ = fr₂ := by
  apply Option.some.inj
  exact h₁.symm.trans h₂
--最終的にはlegacyを外してScopedTypedState_of_concreteにする
theorem legacyScopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ := by
  intro h
  refine
    { stackAligned := ?_
      frameDeclBinding := ?_
      objectBindingsSound := ?_
      refBindingsSound := ?_
      localsExact := ?_
      ownedDisjoint := ?_
      initializedValuesTyped := ?_
      nextFresh := ?_ }
  ·
    exact h.frameDepth
  ·
    intro k Γfr σfr hΓ hσ x d hd
    cases d with
    | object τ =>
        rcases h.objectDeclRealized ⟨Γfr, hΓ, hd⟩ with ⟨a, hbind, hown, hlive⟩
        rcases hbind with ⟨fr', hσ', hbind'⟩
        have hfr : fr' = σfr := frame_eq_of_scope_lookup hσ' hσ
        subst hfr
        exact ⟨.object τ a, hbind', rfl⟩
    | ref τ =>
        rcases h.refDeclRealized ⟨Γfr, hΓ, hd⟩ with ⟨a, hbind, hlive⟩
        rcases hbind with ⟨fr', hσ', hbind'⟩
        have hfr : fr' = σfr := frame_eq_of_scope_lookup hσ' hσ
        subst hfr
        exact ⟨.ref τ a, hbind', rfl⟩
  ·
    intro k Γfr σfr hΓ hσ x τ hd
    rcases h.objectDeclRealized ⟨Γfr, hΓ, hd⟩ with ⟨a, hbind, hown, hlive⟩
    rcases hbind with ⟨fr1, hσ1, hbind1⟩
    rcases hown with ⟨fr2, hσ2, hown2⟩
    rcases hlive with ⟨c, hheap, hty, halive⟩
    have hfr1 : fr1 = σfr := frame_eq_of_scope_lookup hσ1 hσ
    have hfr2 : fr2 = σfr := frame_eq_of_scope_lookup hσ2 hσ
    subst hfr1
    subst hfr2
    exact ⟨a, c, hbind1, hheap, hty, halive, hown2⟩
  ·
    intro k Γfr σfr hΓ hσ x τ hd
    rcases h.refDeclRealized ⟨Γfr, hΓ, hd⟩ with ⟨a, hbind, hlive⟩
    rcases hbind with ⟨fr1, hσ1, hbind1⟩
    rcases hlive with ⟨c, hheap, hty, halive⟩
    have hfr1 : fr1 = σfr := frame_eq_of_scope_lookup hσ1 hσ
    subst hfr1
    exact ⟨a, c, hbind1, hheap, hty, halive⟩
  ·
    intro k fr hσk a
    constructor
    ·
      intro ha
      have hown : runtimeFrameOwnsAddress σ k a := ⟨fr, hσk, ha⟩
      rcases h.ownedAddressNamed hown with ⟨x, τ, hbind⟩
      rcases hbind with ⟨fr', hσ', hbind'⟩
      have hfr : fr' = fr := frame_eq_of_scope_lookup hσ' hσk
      subst hfr
      exact ⟨x, τ, hbind'⟩
    ·
      intro hobj
      rcases hobj with ⟨x, τ, hbind⟩
      have hbindObj : runtimeFrameBindsObject σ k x τ a := ⟨fr, hσk, hbind⟩
      have hown : runtimeFrameOwnsAddress σ k a := by
        exact h.objectsOwned k x τ a hbindObj
      rcases hown with ⟨fr', hσ', ha⟩
      have hfr : fr' = fr := frame_eq_of_scope_lookup hσ' hσk
      subst hfr
      exact ha
  ·
    exact h.ownedDisjoint
  ·
    exact heapInitializedValuesTyped_of_concrete h
  ·
    exact h.nextFresh
/-
axiom legacyScopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ-/

def BodyReadyCI.toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyStructuralBoundary Γ st :=
  { wf := h.wf
    typed0 := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

def BodyReadyCI.toProfile
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyControlProfile Γ st :=
  { summary := { normalOut := h.summary.normalOut, returnOut := h.summary.returnOut } }

def BodyReadyCI.toDynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  { state := h.state, safe := h.safe }

def BodyReadyCI.toAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyAdequacyCI Γ σ st h.toProfile := by
  refine { normalSound := ?_, returnSound := ?_ }
  · intro σ' hstep; exact h.normalSound hstep
  · intro rv σ' hstep; exact h.returnSound hstep

def BodyReadyCI.toClosureBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI h.toStructural h.toProfile h.toDynamic h.toAdequacy

def BlockBodyReadyCI.toStructural
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyStructuralBoundary Γ ss :=
  { wf := h.wf, typed0 := h.typed0, breakScoped := h.breakScoped, continueScoped := h.continueScoped }

def BlockBodyReadyCI.toProfile
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyControlProfile Γ ss :=
  { summary := { normalOut := h.summary.normalOut, returnOut := h.summary.returnOut } }

def BlockBodyReadyCI.toDynamic
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyDynamicBoundary Γ σ ss :=
  { state := h.state, safe := h.safe }

def BlockBodyReadyCI.toAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyAdequacyCI Γ σ ss h.toProfile := by
  refine { normalSound := ?_, returnSound := ?_ }
  · intro σ' hstep; exact h.normalSound hstep
  · intro rv σ' hstep; exact h.returnSound hstep

def BlockBodyReadyCI.toClosureBoundary
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  mkBlockBodyClosureBoundaryCI h.toStructural h.toProfile h.toDynamic h.toAdequacy

def BodyClosureBoundaryCI.toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReadyCI Γ σ st := by
  refine
    { wf := h.structural.wf
      typed0 := h.structural.typed0
      breakScoped := h.structural.breakScoped
      continueScoped := h.structural.continueScoped
      state := h.dynamic.state
      safe := h.dynamic.safe
      summary := { normalOut := h.profile.summary.normalOut, returnOut := h.profile.summary.returnOut }
      normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep; simpa using h.adequacy.normalSound hstep
  · intro rv σ' hstep; simpa using h.adequacy.returnSound hstep

def BlockBodyClosureBoundaryCI.toBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    BlockBodyReadyCI Γ σ ss := by
  refine
    { wf := h.structural.wf
      typed0 := h.structural.typed0
      breakScoped := h.structural.breakScoped
      continueScoped := h.structural.continueScoped
      state := h.dynamic.state
      safe := h.dynamic.safe
      summary := { normalOut := h.profile.summary.normalOut, returnOut := h.profile.summary.returnOut }
      normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep; simpa using h.adequacy.normalSound hstep
  · intro rv σ' hstep; simpa using h.adequacy.returnSound hstep

def legacyStmtReady_of_structural_dynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundary Γ st)
    (hd : BodyDynamicBoundary Γ σ st) :
    StmtReady Γ σ st :=
  ⟨hs.typed0, noUninit_of_stmtReadyConcrete hd.safe, noInvalidRef_of_stmtReadyConcrete hd.safe⟩

def mkLegacyBodyReadyOfStructuralDynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundary Γ st)
    (hd : BodyDynamicBoundary Γ σ st) :
    BodyReady Γ σ st :=
  { wf := hs.wf
    typed := hs.typed0
    breakScoped := hs.breakScoped
    continueScoped := hs.continueScoped
    state := legacyScopedTypedState_of_concrete hd.state
    safe := legacyStmtReady_of_structural_dynamic hs hd }

def BodyClosureBoundaryCI.toBodyReady
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReady Γ σ st :=
  mkLegacyBodyReadyOfStructuralDynamic h.structural h.dynamic

def BodyReadyCI.toBodyReadyViaClosure
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyReady Γ σ st :=
  h.toClosureBoundary.toBodyReady

end Cpp
