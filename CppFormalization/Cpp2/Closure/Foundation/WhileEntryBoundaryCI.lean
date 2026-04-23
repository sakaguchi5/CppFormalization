import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.ReadinessInversions
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI

namespace Cpp

/-!
# Closure.Foundation.WhileEntryBoundaryCI

Canonical current-entry boundary for a top-level `while`.

Role:
- isolate exactly the static/dynamic facts that belong to the current header
  entry;
- do *not* include loop-body local adequacy or post-step reentry laws;
- make `while` entry decomposition theorem-backed from the assembled boundary,
  once a canonical CI entry witness is threaded through that boundary.
-/

structure WhileEntryBoundaryCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)
  hN : HasTypeStmtCI .normalK Γ body Γ
  hB : HasTypeStmtCI .breakK Γ body Γ
  hC : HasTypeStmtCI .continueK Γ body Γ
  state : ScopedTypedStateConcrete Γ σ
  condReady : ExprReadyConcrete Γ σ c (.base .bool)
  bodyReady : StmtReadyConcrete Γ σ body

namespace WhileEntryBoundaryCI

/-- Forget the local `while` header entry back to ordinary statement readiness. -/
@[simp] theorem stmtReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    StmtReadyConcrete Γ σ (.whileStmt c body) := by
  exact StmtReadyConcrete.whileStmt h.hc h.condReady h.bodyReady

/-- The dynamic loop-body entry induced by a `while` header entry. -/
def toLoopBodyDynamic
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    LoopBodyDynamicBoundary Γ σ body :=
  { state := h.state
    safe := h.bodyReady }

/-- The closed-at-start loop-body profile induced by a `while` header entry. -/
def toLoopBodyProfile
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntryBoundaryCI Γ σ c body) :
    LoopBodyControlProfile Γ body := by
  refine
    { summary :=
        { normalOut := some ⟨Γ, h.hN⟩
          breakOut := some ⟨Γ, h.hB⟩
          continueOut := some ⟨Γ, h.hC⟩
          returnOut := none }
      normalClosed := ?_
      breakClosed := ?_
      continueClosed := ?_ }
  · exact ⟨h.hN, rfl⟩
  · exact ⟨h.hB, rfl⟩
  · exact ⟨h.hC, rfl⟩

end WhileEntryBoundaryCI

private theorem while_entry_static_of_bodyEntry
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (e : BodyEntryWitness Γ (.whileStmt c body)) :
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ := by
  cases e with
  | normal out =>
      rcases while_normal_typing_data out.2 with ⟨_, hc, hN, hB, hC⟩
      exact ⟨hc, hN, hB, hC⟩
  | returned out =>
      cases out with
      | mk Δ hR =>
          cases hR with
          | while_return hc hN hB hC _ =>
              exact ⟨hc, hN, hB, hC⟩

/-- Canonical decomposition of an assembled top-level `while` entry. -/
def whileEntryBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileEntryBoundaryCI Γ σ c body := by
  intro h
  rcases while_entry_static_of_bodyEntry h.entry with ⟨hc, hN, hB, hC⟩
  refine
    { hc := hc
      hN := hN
      hB := hB
      hC := hC
      state := h.dynamic.state
      condReady := ?_
      bodyReady := ?_ }
  · exact stmtReadyConcrete_while_cond h.dynamic.safe
  · exact stmtReadyConcrete_while_body h.dynamic.safe

end Cpp
