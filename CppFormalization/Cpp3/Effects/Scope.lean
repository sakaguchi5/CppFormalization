import CppFormalization.Cpp3.Effects.Stmt

/-!
# CppFormalization.Cpp3.Effects.Scope

Scope-facing effect surfaces.

These records name the static shape of declaration binding and block scope
opening/closing.  They do not model runtime lifetime safety; that belongs to
SafetyFragment/Boundary/Stability.
-/

namespace Cpp3
namespace Effects

/-- Declaration scope effect: a declaration may bind a name and may read names in
its initializer or reference target. -/
structure DeclScopeEffect (Γ Δ : TypeEnv) (d : CppDecl) : Type where
  decl : DeclEffect Γ Δ d

namespace DeclScopeEffect

def readsName {Γ Δ : TypeEnv} {d : CppDecl}
    (h : DeclScopeEffect Γ Δ d) : NameSet :=
  h.decl.readsName

def bindsName {Γ Δ : TypeEnv} {d : CppDecl}
    (h : DeclScopeEffect Γ Δ d) : NameSet :=
  h.decl.bindsName

end DeclScopeEffect

/-- Static block-scope effect.

A block opens a static scope, runs an opened body, and returns to the public outer
static environment.  Runtime local lifetime ending is intentionally only named
as a later effect obligation; it is not proven here. -/
structure BlockScopeEffect
    (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Type where
  entry : Static.StaticBlockScopeEntry Γ Γopen
  bodyEffect : BlockEffect Γopen body
  exit : Static.StaticBlockScopeExit Γ Γopen Θ Δ

namespace BlockScopeEffect

def readsName
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeEffect Γ Γopen Θ Δ body) : NameSet :=
  h.bodyEffect.readsName

def writesDirectName
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeEffect Γ Γopen Θ Δ body) : NameSet :=
  h.bodyEffect.writesDirectName

def bindsName
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeEffect Γ Γopen Θ Δ body) : NameSet :=
  h.bodyEffect.bindsName

/-- Names whose bindings are local to the opened block body, syntactically. -/
def localBindsName
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeEffect Γ Γopen Θ Δ body) : NameSet :=
  h.bodyEffect.bindsName

end BlockScopeEffect

/-- The lifecycle event that block exit will later have to justify: local storage
owned by the opened block may end when the block closes. -/
structure BlockCloseLifetimeEffect
    (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Type where
  scope : BlockScopeEffect Γ Γopen Θ Δ body

namespace BlockCloseLifetimeEffect

/-- Names whose local lifetime may end when the block closes. -/
def mayEndLocalLifetime
    {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockCloseLifetimeEffect Γ Γopen Θ Δ body) : NameSet :=
  h.scope.localBindsName

end BlockCloseLifetimeEffect

end Effects
end Cpp3
