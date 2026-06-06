import CppFormalization.Cpp3.Typing.Micro.All

namespace Cpp3
namespace Typing
namespace Judgment

/-!
# CppFormalization.Cpp3.Typing.Judgment.Stmt

Control-indexed statement and block-body typing reconstructed from the micro
typing components.

The primitive cases are supplied by `Typing.Micro.PrimitiveTyping`.  The
compound cases expose the old mutual-typing shape, but keep the important
decomposition points visible:

* normal sequencing/block-cons uses a head-normal component and a tail component;
* abrupt sequencing/block-cons short-circuits through an explicit `AbruptKind`;
* branch/while/block use Micro static payloads rather than baking their
  decomposition directly into the public judgment;
* runtime continuation safety is not asserted here.  It belongs to the
  obligation slots and later programmer-facing contracts.
-/

mutual

/-- Control-indexed statement typing for Cpp3.

Read `StmtTyping k Γ st Δ` as: statement `st`, started in type environment `Γ`,
has a static route classified by control kind `k` and exits with type
environment `Δ`. -/
inductive StmtTyping : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop where
  /-- Primitive statements are typed by the primitive micro package. -/
  | primitive
      {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv} :
      Micro.PrimitiveTyping Γ st k Δ →
      StmtTyping k Γ st Δ

  /-- Static normal bind for `s; t`.

  This is the statement-level reconstruction of the normal half of sequencing.
  Post-state continuation safety is intentionally not included here. -/
  | seqNormal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt} :
      StmtTyping .normalK Γ s Θ →
      StmtTyping k Θ t Δ →
      StmtTyping k Γ (.seq s t) Δ

  /-- Static abrupt short-circuit for `s; t`.

  If the head is statically classified by an abrupt control kind, the tail is not
  consumed by that channel. -/
  | seqAbrupt
      {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt} :
      Micro.AbruptKind k →
      StmtTyping k Γ s Δ →
      StmtTyping k Γ (.seq s t) Δ

  /-- Branch merge for `if c then s else t`.

  The constructor consumes the Micro-level `IteStatic` payload, so the condition
  typing and same-channel/same-exit branch merge stay available as separate
  components for later projection/inversion layers. -/
  | ite
    {k : ControlKind} {Γ Δ : TypeEnv}
    {c : ValExpr} {s t : CppStmt} :
    Micro.Composition.ConditionBoolStatic Γ c →
    StmtTyping k Γ s Δ →
    StmtTyping k Γ t Δ →
    StmtTyping k Γ (.ite c s t) Δ

  /-- Static while-normal route.

  The constructor consumes the Micro-level static while payload.  Runtime
  backedge/reentry safety is intentionally not asserted here. -/
  | whileNormal
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    Micro.Composition.WhileConditionStatic Γ c →
    StmtTyping .normalK Γ body Γ →
    StmtTyping .breakK Γ body Γ →
    StmtTyping .continueK Γ body Γ →
    StmtTyping .normalK Γ (.whileStmt c body) Γ

| whileReturn
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    Micro.Composition.WhileConditionStatic Γ c →
    StmtTyping .normalK Γ body Γ →
    StmtTyping .breakK Γ body Γ →
    StmtTyping .continueK Γ body Γ →
    StmtTyping .returnK Γ body Δ →
    StmtTyping .returnK Γ (.whileStmt c body) Δ

  /-- Block statement.

  The public surface is kept C++-natural: a block statement exits back at the
  outer type environment `Γ`.  The Micro payload still exposes the opened scope
  `Γopen`, the opened body exit `Θ`, and the explicit scope-exit component. -/
  | block
    {k : ControlKind} {Γ Γopen Θ : TypeEnv} {ss : StmtBlock} :
    Micro.Composition.BlockScopeEntryStatic Γ Γopen →
    BlockTyping k Γopen ss Θ →
    Micro.Composition.BlockScopeExitStatic Γ Γopen Θ Γ →
    StmtTyping k Γ (.block ss) Γ

/-- Control-indexed block-body typing for Cpp3. -/
inductive BlockTyping : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop where
  /-- Empty block bodies finish normally and preserve the type environment. -/
  | nil
      {Γ : TypeEnv} :
      BlockTyping .normalK Γ .nil Γ

  /-- Static normal block-cons. -/
  | consNormal
      {k : ControlKind} {Γ Θ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock} :
      StmtTyping .normalK Γ head Θ →
      BlockTyping k Θ tail Δ →
      BlockTyping k Γ (.cons head tail) Δ

  /-- Static abrupt block-cons short-circuit. -/
  | consAbrupt
      {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock} :
      Micro.AbruptKind k →
      StmtTyping k Γ head Δ →
      BlockTyping k Γ (.cons head tail) Δ

end

end Judgment
end Typing
end Cpp3
