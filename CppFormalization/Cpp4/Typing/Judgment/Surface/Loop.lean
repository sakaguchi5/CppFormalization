import CppFormalization.Cpp4.Typing.Judgment.Surface.Stmt
import CppFormalization.Cpp4.Typing.Judgment.Plan.Loop

/-!
# CppFormalization.Cpp4.Typing.Judgment.Surface.Loop

Surface loop typing certificates.
-/

namespace Cpp4

namespace SurfaceLoopTyping

/-- Surface `while` loop. -/
def whileLoop {Γ : TypeEnv} {κ : ControlContext} {c : CppCond} {body : CppStmt}
    (hCond : CondTyping Γ c)
    (hBody : SurfaceStmtTyping Γ (ControlContext.loopBody κ) body) :
    SurfaceLoopTyping Γ κ (.whileLoop c body) where
  demand := LoopDemand.preTest hCond.demand {
    demands := hBody.demand.demands
  }
  formation := hCond.formation ∧ hBody.formation
  evidence := And.intro hCond.evidence hBody.evidence

/-- Surface `do while` loop. -/
def doWhileLoop {Γ : TypeEnv} {κ : ControlContext} {body : CppStmt} {c : CppCond}
    (hBody : SurfaceStmtTyping Γ (ControlContext.loopBody κ) body)
    (hCond : CondTyping Γ c) :
    SurfaceLoopTyping Γ κ (.doWhileLoop body c) where
  demand := LoopDemand.postTest {
    demands := hBody.demand.demands
  } hCond.demand
  formation := hBody.formation ∧ hCond.formation
  evidence := And.intro hBody.evidence hCond.evidence

/-- Surface `for` loop.  The initializer may extend the loop-local environment;
the optional condition, body, and iteration step are checked in that environment. -/
def forLoop {Γ : TypeEnv} {κ : ControlContext}
    {init : CppForInit} {cond : Option CppCond} {iter : CppForIter} {body : CppStmt}
    (hInit : ForInitTyping Γ init)
    (hCond : OptionalCondTyping hInit.target cond)
    (hIter : ForIterTyping hInit.target iter)
    (hBody : SurfaceStmtTyping hInit.target (ControlContext.loopBody κ) body) :
    SurfaceLoopTyping Γ κ (.forLoop init cond iter body) where
  demand := LoopDemand.forFrame hInit.demand hCond.demand hIter.demand {
    demands := hBody.demand.demands
  }
  formation := hInit.formation ∧ hCond.formation ∧ hIter.formation ∧ hBody.formation
  evidence :=
    And.intro hInit.evidence
      (And.intro hCond.evidence (And.intro hIter.evidence hBody.evidence))

end SurfaceLoopTyping

namespace SurfaceStmtTyping

/-- Surface loop statement.  Loop-local ordinary-name environment effects do not
escape the loop. -/
def loop {Γ : TypeEnv} {κ : ControlContext} {l : CppLoop}
    (hLoop : SurfaceLoopTyping Γ κ l) : SurfaceStmtTyping Γ κ (.loop l) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.loopFrame hLoop.demand)
  formation := hLoop.formation
  evidence := hLoop.evidence

end SurfaceStmtTyping

end Cpp4
