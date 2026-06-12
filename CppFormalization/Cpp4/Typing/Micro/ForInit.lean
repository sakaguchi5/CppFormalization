import CppFormalization.Cpp4.Typing.Micro.Decl

/-!
# CppFormalization.Cpp4.Typing.Micro.ForInit

Micro typing for the restricted Cpp4 `for` initializer surface.
-/

namespace Cpp4

/-- Micro typing certificate for `for` initializers.  Unlike iteration
expressions, an initializer may introduce an ordinary name. -/
structure ForInitTyping (Γ : TypeEnv) (init : CppForInit) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : AtomDemand
  formation : Prop
  evidence : formation

namespace ForInitTyping

/-- Empty for-initializer. -/
def none (Γ : TypeEnv) : ForInitTyping Γ .none where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := AtomDemand.skip
  formation := True
  evidence := trivial

/-- Expression-statement for-initializer. -/
def expr {Γ : TypeEnv} {s : CppExprStmt}
    (h : ExprStmtTyping Γ s) : ForInitTyping Γ (.expr s) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := h.demand
  formation := h.formation
  evidence := h.evidence

/-- Declaration for-initializer. -/
def decl {Γ : TypeEnv} {d : CppDecl}
    (h : DeclTyping Γ d) : ForInitTyping Γ (.decl d) where
  target := h.target
  envEffect := h.envEffect
  demand := h.demand
  formation := h.formation
  evidence := h.evidence

end ForInitTyping

end Cpp4
