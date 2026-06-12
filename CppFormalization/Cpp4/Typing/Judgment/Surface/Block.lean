import CppFormalization.Cpp4.Typing.Judgment.Surface.Stmt

/-!
# CppFormalization.Cpp4.Typing.Judgment.Surface.Block

Surface block typing certificates.
-/

namespace Cpp4

namespace SurfaceBlockTyping

/-- Empty surface block. -/
def nil (Γ : TypeEnv) (κ : ControlContext) : SurfaceBlockTyping Γ κ .nil where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := { demands := [] }
  formation := True
  evidence := trivial

/-- Cons a typed surface statement in front of a typed surface block.  The tail is
typed in the post-environment produced by the head statement. -/
def cons {Γ : TypeEnv} {κ : ControlContext} {head : CppStmt} {tail : StmtBlock}
    (hHead : SurfaceStmtTyping Γ κ head)
    (hTail : SurfaceBlockTyping hHead.target κ tail) :
    SurfaceBlockTyping Γ κ (.cons head tail) where
  target := hTail.target
  envEffect := TypeEnvEffect.compose hHead.envEffect hTail.envEffect
  demand := { demands := hHead.demand.demands ++ hTail.demand.demands }
  formation := hHead.formation ∧ hTail.formation
  evidence := And.intro hHead.evidence hTail.evidence

end SurfaceBlockTyping

end Cpp4
