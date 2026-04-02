import CppFormalization.Cpp2.Closure.Legacy.ReadinessFacade
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

namespace ClosureV2

/--
Stage 3 temporary bridge.

`ClosureRefactoring` branch ではまだ
`ScopedTypedStateConcrete Γ σ -> ScopedTypedState Γ σ`
が theorem/axiom として提供されていない。
old coarse facade `BodyReady` を legacy compatibility として再構成するために、
ここではその bridge を互換層の局所 obligation として明示する。
-/
axiom legacyScopedTypedState_of_concrete
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedState Γ σ

end ClosureV2

/-!
# Closure.Foundation.BodyBoundaryCompatibility

第3段階の互換層。

目的:
- 新 assembled boundary (`Cpp.ClosureV2.BodyClosureBoundaryCI`) と既存
  `BodyReadyCI` / `BlockBodyReadyCI` の間を相互変換できるようにする。
- old coarse external facade `BodyReady` を、新 structural + dynamic 側から
  再構成できるようにする。
-/

def BodyReadyCI.toStructuralV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ClosureV2.BodyStructuralBoundary Γ st :=
  { wf := h.wf
    typed0 := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

def BodyReadyCI.toProfileV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ClosureV2.BodyControlProfile Γ st :=
  { summary :=
      { normalOut := h.summary.normalOut
        returnOut := h.summary.returnOut } }

def BodyReadyCI.toDynamicV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ClosureV2.BodyDynamicBoundary Γ σ st :=
  { state := h.state
    safe := h.safe }

def BodyReadyCI.toAdequacyV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ClosureV2.BodyAdequacyCI Γ σ st h.toProfileV2 := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    exact h.normalSound hstep
  · intro rv σ' hstep
    exact h.returnSound hstep

def BodyReadyCI.toClosureBoundaryV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    ClosureV2.BodyClosureBoundaryCI Γ σ st :=
  ClosureV2.mkBodyClosureBoundaryCI
    h.toStructuralV2
    h.toProfileV2
    h.toDynamicV2
    h.toAdequacyV2

def BlockBodyReadyCI.toStructuralV2
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    ClosureV2.BlockBodyStructuralBoundary Γ ss :=
  { wf := h.wf
    typed0 := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

def BlockBodyReadyCI.toProfileV2
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    ClosureV2.BlockBodyControlProfile Γ ss :=
  { summary :=
      { normalOut := h.summary.normalOut
        returnOut := h.summary.returnOut } }

def BlockBodyReadyCI.toDynamicV2
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    ClosureV2.BlockBodyDynamicBoundary Γ σ ss :=
  { state := h.state
    safe := h.safe }

def BlockBodyReadyCI.toAdequacyV2
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    ClosureV2.BlockBodyAdequacyCI Γ σ ss h.toProfileV2 := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    exact h.normalSound hstep
  · intro rv σ' hstep
    exact h.returnSound hstep

def BlockBodyReadyCI.toClosureBoundaryV2
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyCI Γ σ ss) :
    ClosureV2.BlockBodyClosureBoundaryCI Γ σ ss :=
  ClosureV2.mkBlockBodyClosureBoundaryCI
    h.toStructuralV2
    h.toProfileV2
    h.toDynamicV2
    h.toAdequacyV2

def ClosureV2.BodyClosureBoundaryCI.toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : ClosureV2.BodyClosureBoundaryCI Γ σ st) :
    BodyReadyCI Γ σ st := by
  refine
    { wf := h.structural.wf
      typed0 := h.structural.typed0
      breakScoped := h.structural.breakScoped
      continueScoped := h.structural.continueScoped
      state := h.dynamic.state
      safe := h.dynamic.safe
      summary :=
        { normalOut := h.profile.summary.normalOut
          returnOut := h.profile.summary.returnOut }
      normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    simpa using h.adequacy.normalSound hstep
  · intro rv σ' hstep
    simpa using h.adequacy.returnSound hstep

def ClosureV2.BlockBodyClosureBoundaryCI.toBlockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : ClosureV2.BlockBodyClosureBoundaryCI Γ σ ss) :
    BlockBodyReadyCI Γ σ ss := by
  refine
    { wf := h.structural.wf
      typed0 := h.structural.typed0
      breakScoped := h.structural.breakScoped
      continueScoped := h.structural.continueScoped
      state := h.dynamic.state
      safe := h.dynamic.safe
      summary :=
        { normalOut := h.profile.summary.normalOut
          returnOut := h.profile.summary.returnOut }
      normalSound := ?_
      returnSound := ?_ }
  · intro σ' hstep
    simpa using h.adequacy.normalSound hstep
  · intro rv σ' hstep
    simpa using h.adequacy.returnSound hstep

/-! ## old coarse external facade `BodyReady` の再構成 -/

def legacyStmtReady_of_structural_dynamicV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : ClosureV2.BodyStructuralBoundary Γ st)
    (hd : ClosureV2.BodyDynamicBoundary Γ σ st) :
    StmtReady Γ σ st :=
  ⟨
    hs.typed0,
    noUninit_of_stmtReadyConcrete hd.safe,
    noInvalidRef_of_stmtReadyConcrete hd.safe
  ⟩

def mkLegacyBodyReadyOfStructuralDynamicV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hs : ClosureV2.BodyStructuralBoundary Γ st)
    (hd : ClosureV2.BodyDynamicBoundary Γ σ st) :
    BodyReady Γ σ st :=
  { wf := hs.wf
    typed := hs.typed0
    breakScoped := hs.breakScoped
    continueScoped := hs.continueScoped
    state := ClosureV2.legacyScopedTypedState_of_concrete hd.state
    safe := legacyStmtReady_of_structural_dynamicV2 hs hd }

/-- Forget V2 profile/adequacy and recover the old coarse external body boundary. -/
def ClosureV2.BodyClosureBoundaryCI.toBodyReady
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : ClosureV2.BodyClosureBoundaryCI Γ σ st) :
    BodyReady Γ σ st :=
  mkLegacyBodyReadyOfStructuralDynamicV2 h.structural h.dynamic

/-- The same coarse external facade can be recovered from the legacy CI boundary as well. -/
def BodyReadyCI.toBodyReadyViaV2
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReadyCI Γ σ st) :
    BodyReady Γ σ st :=
  h.toClosureBoundaryV2.toBodyReady

end Cpp
