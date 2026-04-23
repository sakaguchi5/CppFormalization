import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI

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
      let ⟨hN, hB, hC, hR⟩ := while_return_typing_data out.2
      some ⟨out.1, hR⟩

def whileEntryBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileEntryBoundaryCI Γ σ c body := by
  intro h
  rcases while_entry_static_of_root h.static.root with ⟨hc, hN, hB, hC⟩
  refine
    { hc := hc
      hN := hN
      hB := hB
      hC := hC
      hR? := while_body_returnOut?_of_static h.static
      state := h.dynamic.state
      condReady := ?_
      bodyReady := ?_ }
  · exact stmtReadyConcrete_while_cond h.dynamic.safe
  · exact stmtReadyConcrete_while_body h.dynamic.safe

end Cpp
