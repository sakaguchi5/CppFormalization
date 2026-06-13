import CppFormalization.Cpp4.Boundary.Place
import CppFormalization.Cpp4.Typing.Micro.CallArgs

/-!
# CppFormalization.Cpp4.Boundary.Expr

Runtime boundaries for typed value expressions and conditions.
-/

namespace Cpp4

/-- A typed value expression is enterable when its generated expression demand is satisfied. -/
structure ExprBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {e : ValExpr}
    (h : ExprTyping Γ e) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace ExprBoundary

/-- Repackage an expression boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {e : ValExpr}
    {h : ExprTyping Γ e} (b : ExprBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build an expression boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {e : ValExpr}
    {h : ExprTyping Γ e} (b : DemandBoundary χ σ h.demand.demands) :
    ExprBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the expression typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {e : ValExpr}
    {h : ExprTyping Γ e} (_b : ExprBoundary χ σ h) : h.formation :=
  h.evidence

end ExprBoundary

/-- A typed boolean-like condition is enterable when its expression demand is satisfied. -/
structure CondBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {c : CppCond}
    (h : CondTyping Γ c) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace CondBoundary

/-- Repackage a condition boundary as an expression-demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {c : CppCond}
    {h : CondTyping Γ c} (b : CondBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a condition boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {c : CppCond}
    {h : CondTyping Γ c} (b : DemandBoundary χ σ h.demand.demands) :
    CondBoundary χ σ h where
  demandsSatisfied := b.satisfied

end CondBoundary

end Cpp4
