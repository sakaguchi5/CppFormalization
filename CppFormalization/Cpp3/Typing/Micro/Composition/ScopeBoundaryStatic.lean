import CppFormalization.Cpp3.Typing.Micro.Composition.WhileStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.ScopeBoundaryStatic

Static scope-boundary components for block statements.

A C++ block statement is not just a block body: it opens a scope, checks the
opened body, and exits back to the outer type environment.  This file exposes
that static shape without asserting runtime opened-body adequacy or close-scope
preservation.
-/

/-- Static entry into a block scope.

For the current Cpp3 core this is exactly `pushTypeScope Γ`.  It is kept as an
explicit component so later boundary layers can talk about opened block bodies
without baking the entry step into the public statement judgment. -/
structure BlockScopeEntryStatic
    (Γ Γopen : TypeEnv) : Prop where
  opened : Γopen = pushTypeScope Γ

namespace BlockScopeEntryStatic

/-- The canonical block-scope entry. -/
def canonical (Γ : TypeEnv) :
    BlockScopeEntryStatic Γ (pushTypeScope Γ) :=
  ⟨rfl⟩

/-- Project the certified opened-scope equality. -/
def certifiedOpened
    {Γ Γopen : TypeEnv}
    (h : BlockScopeEntryStatic Γ Γopen) :
    Contracts.Certified (Γopen = pushTypeScope Γ) :=
  h.opened

end BlockScopeEntryStatic

/-- Static opened block-body payload.

This component deliberately says only that the block body is checked inside the
opened type environment.  Runtime opened-body readiness/adequacy belongs to a
later boundary layer. -/
structure BlockOpenedBodyStatic
    (JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop)
    (k : ControlKind) (Γopen Θ : TypeEnv) (body : StmtBlock) : Prop where
  bodyTyping : JBlock k Γopen body Θ

namespace BlockOpenedBodyStatic

/-- Project the certified opened-body typing evidence. -/
def certifiedBody
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γopen Θ : TypeEnv} {body : StmtBlock}
    (h : BlockOpenedBodyStatic JBlock k Γopen Θ body) :
    Contracts.Certified (JBlock k Γopen body Θ) :=
  h.bodyTyping

end BlockOpenedBodyStatic

/-- Static exit from a block statement back to the outer type environment.

`Θ` is the opened body's internal exit environment.  The statement-level exit is
`Δ`, which is required to be the outer environment `Γ`. -/
structure BlockScopeExitStatic
    (Γ Γopen Θ Δ : TypeEnv) : Prop where
  closed : Δ = Γ

namespace BlockScopeExitStatic

/-- Canonical statement-level block exit. -/
def canonical (Γ Γopen Θ : TypeEnv) :
    BlockScopeExitStatic Γ Γopen Θ Γ :=
  ⟨rfl⟩

/-- Project the certified statement-level exit equality. -/
def certifiedClosed
    {Γ Γopen Θ Δ : TypeEnv}
    (h : BlockScopeExitStatic Γ Γopen Θ Δ) :
    Contracts.Certified (Δ = Γ) :=
  h.closed

end BlockScopeExitStatic

/-- Complete static payload for a block statement.

The public statement judgment can reconstruct the old block constructor from
this payload, while later layers can reuse the separated entry/body/exit pieces. -/
structure BlockScopeStatic
    (JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop)
    (k : ControlKind) (Γ Γopen Θ Δ : TypeEnv) (body : StmtBlock) : Prop where
  entry : BlockScopeEntryStatic Γ Γopen
  openedBody : BlockOpenedBodyStatic JBlock k Γopen Θ body
  exit : BlockScopeExitStatic Γ Γopen Θ Δ

namespace BlockScopeStatic

/-- Project the certified scope-entry component. -/
def certifiedEntry
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeStatic JBlock k Γ Γopen Θ Δ body) :
    Contracts.Certified (BlockScopeEntryStatic Γ Γopen) :=
  h.entry

/-- Project the certified opened-body component. -/
def certifiedOpenedBody
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeStatic JBlock k Γ Γopen Θ Δ body) :
    Contracts.Certified (BlockOpenedBodyStatic JBlock k Γopen Θ body) :=
  h.openedBody

/-- Project the certified scope-exit component. -/
def certifiedExit
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Γopen Θ Δ : TypeEnv} {body : StmtBlock}
    (h : BlockScopeStatic JBlock k Γ Γopen Θ Δ body) :
    Contracts.Certified (BlockScopeExitStatic Γ Γopen Θ Δ) :=
  h.exit

end BlockScopeStatic

end Composition
end Micro
end Typing
end Cpp3
