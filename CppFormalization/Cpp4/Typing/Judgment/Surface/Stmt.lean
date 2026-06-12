import CppFormalization.Cpp4.Typing.Judgment.Plan.Plan
import CppFormalization.Cpp4.Typing.Micro.Decl
import CppFormalization.Cpp4.Resource.Demand.Surface

/-!
# CppFormalization.Cpp4.Typing.Judgment.Surface.Stmt

Surface statement typing certificates.

This layer types C++-shaped surface statements directly.  It does not replace the
ControlPlan-centered judgment; it records the surface-side environment effect,
formation evidence, and typed demand that the later expansion-preservation layer
will connect to `Typing.Judgment.Plan`.
-/

namespace Cpp4

/-- A typed surface statement with its ordinary-name environment effect and typed
surface demand. -/
structure SurfaceStmtTyping (Γ : TypeEnv) (κ : ControlContext) (s : CppStmt) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SurfaceStmtDemand
  formation : Prop
  evidence : formation

/-- A typed surface statement block.  Constructors live in `Surface.Block`. -/
structure SurfaceBlockTyping (Γ : TypeEnv) (κ : ControlContext) (b : StmtBlock) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SurfaceBlockDemand
  formation : Prop
  evidence : formation

/-- A typed surface loop.  Constructors live in `Surface.Loop`. -/
structure SurfaceLoopTyping (Γ : TypeEnv) (κ : ControlContext) (l : CppLoop) : Type where
  demand : LoopDemand
  formation : Prop
  evidence : formation

/-- A typed surface switch statement.  Constructors live in `Surface.Switch`. -/
structure SurfaceSwitchTyping
    (Γ : TypeEnv) (κ : ControlContext) (cond : CppSwitchCond) (arms : SwitchArmList) : Type where
  demand : SwitchDemand
  formation : Prop
  evidence : formation

namespace SurfaceStmtTyping

/-- Surface `skip`. -/
def skip (Γ : TypeEnv) (κ : ControlContext) : SurfaceStmtTyping Γ κ .skip where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.atom AtomDemand.skip)
  formation := True
  evidence := trivial

/-- Surface expression statement. -/
def exprStmt {Γ : TypeEnv} {κ : ControlContext} {s : CppExprStmt}
    (h : ExprStmtTyping Γ s) : SurfaceStmtTyping Γ κ (.exprStmt s) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.atom h.demand)
  formation := h.formation
  evidence := h.evidence

/-- Surface assignment statement. -/
def assign {Γ : TypeEnv} {κ : ControlContext} {a : CppAssign}
    (h : AssignTyping Γ a) : SurfaceStmtTyping Γ κ (.assign a) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.atom h.demand)
  formation := h.formation
  evidence := h.evidence

/-- Surface declaration statement. -/
def decl {Γ : TypeEnv} {κ : ControlContext} {d : CppDecl}
    (h : DeclTyping Γ d) : SurfaceStmtTyping Γ κ (.decl d) where
  target := h.target
  envEffect := h.envEffect
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.atom h.demand)
  formation := h.formation
  evidence := h.evidence

/-- Surface sequencing.  The right statement is typed in the post-environment of
left. -/
def seq {Γ : TypeEnv} {κ : ControlContext} {head tail : CppStmt}
    (hHead : SurfaceStmtTyping Γ κ head)
    (hTail : SurfaceStmtTyping hHead.target κ tail) :
    SurfaceStmtTyping Γ κ (.seq head tail) where
  target := hTail.target
  envEffect := TypeEnvEffect.compose hHead.envEffect hTail.envEffect
  demand := { demands := hHead.demand.demands ++ hTail.demand.demands }
  formation := hHead.formation ∧ hTail.formation
  evidence := And.intro hHead.evidence hTail.evidence

/-- Surface branch.  Branch-local ordinary-name environment effects do not escape
this surface statement. -/
def ite {Γ : TypeEnv} {κ : ControlContext} {c : CppCond} {thenStmt elseStmt : CppStmt}
    (hCond : CondTyping Γ c)
    (hThen : SurfaceStmtTyping Γ κ thenStmt)
    (hElse : SurfaceStmtTyping Γ κ elseStmt) :
    SurfaceStmtTyping Γ κ (.ite c thenStmt elseStmt) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand :=
    { demands := hCond.demand.demands ++ hThen.demand.demands ++ hElse.demand.demands }
  formation := hCond.formation ∧ hThen.formation ∧ hElse.formation
  evidence := And.intro hCond.evidence (And.intro hThen.evidence hElse.evidence)

/-- Surface block statement.  The block body is typed internally, but its ordinary
name environment effect does not escape the block statement. -/
def block {Γ : TypeEnv} {κ : ControlContext} {b : StmtBlock}
    (hBody : SurfaceBlockTyping Γ κ b) : SurfaceStmtTyping Γ κ (.block b) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.scopeFrame {
    demands := hBody.demand.demands
  })
  formation := hBody.formation
  evidence := hBody.evidence

/-- Surface jump statement. -/
def jump {Γ : TypeEnv} {κ : ControlContext} {j : CppJump}
    (h : JumpTyping κ j) : SurfaceStmtTyping Γ κ (.jump j) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.atom h.demand)
  formation := True
  evidence := trivial

end SurfaceStmtTyping

end Cpp4
