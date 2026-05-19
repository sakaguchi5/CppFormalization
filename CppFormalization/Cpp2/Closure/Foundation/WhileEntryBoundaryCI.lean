import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Safety.ReadinessInversions
import CppFormalization.Cpp2.Boundary.LoopBody.All

namespace Cpp

/-!
# Closure.Foundation.WhileEntryBoundaryCI

Canonical current-entry boundary for a top-level `while`.

Redesign:
- read static information from `BodyStaticBoundaryCI`,
  not from an ad hoc `entry/profile` split;
- carry the optional body-return channel explicitly;
- keep reentry laws out of this object.
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

private theorem while_entry_static_of_root
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (r : BodyEntryWitness Γ (.whileStmt c body)) :
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ := by
  cases r with
  | normal out =>
      rcases while_normal_typing_data out.2 with ⟨_, hc, hN, hB, hC⟩
      exact ⟨hc, hN, hB, hC⟩
  | returned out =>
      cases out with
      | mk Δ hR =>
          cases hR with
          | while_return hc hN hB hC _ =>
              exact ⟨hc, hN, hB, hC⟩

private def while_body_returnOut?_of_static
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (s : BodyStaticBoundaryCI Γ (.whileStmt c body)) :
    Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ} :=
  match s.profile.summary.returnOut with
  | none => none
  | some out =>
      some ⟨out.1, (while_return_typing_data out.2).2.2.2⟩

def whileEntryBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileEntryBoundaryCI Γ σ c body := by
  intro h
  exact
    { hc := (while_entry_static_of_root h.static.root).1
      hN := (while_entry_static_of_root h.static.root).2.1
      hB := (while_entry_static_of_root h.static.root).2.2.1
      hC := (while_entry_static_of_root h.static.root).2.2.2
      hR? := while_body_returnOut?_of_static h.static
      state := h.dynamic.state
      condReady := stmtReadyConcrete_while_cond h.dynamic.safe
      bodyReady := stmtReadyConcrete_while_body h.dynamic.safe }

/--
Return channel exposed by the entry-projected loop-body profile.

If the top-level `while` static profile has a return channel, then the
`WhileEntryBoundaryCI`-projected loop-body profile exposes the corresponding
body return channel.
-/
theorem whileEntryBoundaryCI_toLoopBodyProfile_returnOut_of_static
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    {outW : {Δ : TypeEnv //
        HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ}}
    (hW : hentry.static.profile.summary.returnOut = some outW) :
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry).toLoopBodyProfile.summary.returnOut =
      some ⟨outW.1, (while_return_typing_data outW.2).2.2.2⟩ := by
  change
    while_body_returnOut?_of_static hentry.static =
      some ⟨outW.1, (while_return_typing_data outW.2).2.2.2⟩
  simp [while_body_returnOut?_of_static, hW]


end Cpp
