import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

private theorem frame_eq_of_scope_lookup
    {σ : State} {k : Nat} {fr₁ fr₂ : ScopeFrame}
    (h₁ : σ.scopes[k]? = some fr₁)
    (h₂ : σ.scopes[k]? = some fr₂) :
    fr₁ = fr₂ := by
  apply Option.some.inj
  exact h₁.symm.trans h₂

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
  · exact h.frameDepth
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
  · exact h.ownedDisjoint
  · exact h.heapStoredValuesTyped
  · exact h.nextFresh

theorem scopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ :=
  legacyScopedTypedState_of_concrete

namespace BodyReadyCI

def toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyStructuralBoundary Γ st :=
  h.structural

def toStatic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyStaticBoundaryCI Γ st :=
  h.static

def toTyped0
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    WellTypedFrom Γ st :=
  h.static.typed0

def toProfile
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyControlProfile Γ st :=
  h.static.profile

def toEntry
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyEntryWitness Γ st :=
  h.static.root

def toDynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyDynamicBoundary Γ σ st :=
  h.dynamic

def toAdequacy
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyAdequacyCI Γ σ st h.static.profile :=
  h.adequacy

def toClosureBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyClosureBoundaryCI Γ σ st :=
  mkBodyClosureBoundaryCI h.structural h.static h.dynamic h.adequacy

end BodyReadyCI

namespace BlockBodyReadyCI

def toStructural
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyStructuralBoundary Γ ss :=
  h.structural

def toStatic
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyStaticBoundaryCI Γ ss :=
  h.static

def toProfile
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyControlProfile Γ ss :=
  h.static.profile

def toEntry
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyEntryWitness Γ ss :=
  h.static.root

def toDynamic
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyDynamicBoundary Γ σ ss :=
  h.dynamic

def toAdequacy
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyAdequacyCI Γ σ ss h.static.profile :=
  h.adequacy

def toClosureBoundary
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    BlockBodyClosureBoundaryCI Γ σ ss :=
  mkBlockBodyClosureBoundaryCI h.structural h.static h.dynamic h.adequacy

end BlockBodyReadyCI

namespace BodyClosureBoundaryCI

def toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReadyCI Γ σ st :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

end BodyClosureBoundaryCI

namespace BlockBodyClosureBoundaryCI

def toBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    BlockBodyReadyCI Γ σ ss :=
  { structural := h.structural
    static := h.static
    dynamic := h.dynamic
    adequacy := h.adequacy }

end BlockBodyClosureBoundaryCI

def legacyStmtReady_of_static_dynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStaticBoundaryCI Γ st)
    (hd : BodyDynamicBoundary Γ σ st) :
    StmtReady Γ σ st :=
  ⟨hs.typed0, noUninit_of_stmtReadyConcrete hd.safe, noInvalidRef_of_stmtReadyConcrete hd.safe⟩

def mkLegacyBodyReadyOfStructuralStaticDynamic
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : BodyStructuralBoundary Γ st)
    (hst : BodyStaticBoundaryCI Γ st)
    (hd : BodyDynamicBoundary Γ σ st) :
    BodyReady Γ σ st :=
  { wf := hs.wf
    typed := hst.typed0
    breakScoped := hs.breakScoped
    continueScoped := hs.continueScoped
    state := legacyScopedTypedState_of_concrete hd.state
    safe := legacyStmtReady_of_static_dynamic hst hd }

def BodyClosureBoundaryCI.toBodyReady
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReady Γ σ st :=
  mkLegacyBodyReadyOfStructuralStaticDynamic h.structural h.static h.dynamic

def BodyReadyCI.toBodyReadyViaClosure
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyReady Γ σ st :=
  h.toClosureBoundary.toBodyReady

end Cpp
