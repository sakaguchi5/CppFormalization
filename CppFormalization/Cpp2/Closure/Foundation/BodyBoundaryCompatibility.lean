import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

axiom legacyScopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ

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
