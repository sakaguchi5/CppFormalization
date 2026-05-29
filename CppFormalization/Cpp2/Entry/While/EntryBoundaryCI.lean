-- removed ideal relayout: import CppFormalization.Cpp2.Boundary.LoopBody.All  -- All.lean excluded
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Static.Typing.ControlIndexed
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.Strengthening
import CppFormalization.Cpp2.Entry.LoopBody.DynamicBoundaryCI
import CppFormalization.Cpp2.Profile.LoopBody.ProfileCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.While.EntryBoundaryCI

Canonical current-entry boundary for a top-level `while`.

This is the boundary object itself.  It records the C++-meaningful data needed
at the current while entry:

* condition typing/readiness;
* loop-body normal/break/continue closed-at-start typing;
* optional loop-body return channel;
* concrete state/readiness for the condition and body.

It deliberately does not know how to project itself from a full
`BodyClosureBoundaryCI`; that compatibility bridge lives in
`Closure.Foundation.WhileEntryBoundaryCompatibilityCI`.
-/

structure WhileEntryBoundaryCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)
  hN : HasTypeStmtCI .normalK Γ body Γ
  hB : HasTypeStmtCI .breakK Γ body Γ
  hC : HasTypeStmtCI .continueK Γ body Γ
  hR? : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ}
  state : ScopedTypedStateConcrete Γ σ
  condReady : ExprReadyConcrete Γ σ c (.base .bool)
  bodyReady : StmtReadyConcrete Γ σ body

namespace WhileEntryBoundaryCI

@[simp] theorem stmtReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    StmtReadyConcrete Γ σ (.whileStmt c body) := by
  exact StmtReadyConcrete.whileStmt h.hc h.condReady h.bodyReady

def toLoopBodyDynamic
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    LoopBodyDynamicBoundary Γ σ body :=
  { state := h.state
    safe := h.bodyReady }

def toLoopBodyProfile
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    LoopBodyControlProfile Γ body := by
  refine
    { summary :=
        { normalOut := some ⟨Γ, h.hN⟩
          breakOut := some ⟨Γ, h.hB⟩
          continueOut := some ⟨Γ, h.hC⟩
          returnOut := h.hR? }
      normalClosed := ?_
      breakClosed := ?_
      continueClosed := ?_ }
  · exact ⟨h.hN, rfl⟩
  · exact ⟨h.hB, rfl⟩
  · exact ⟨h.hC, rfl⟩

end WhileEntryBoundaryCI

end Cpp
