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
* branch/while consume the new `CppCond` condition category through
  `ConditionStatic`;
* block exposes scope entry/opened body/scope exit while keeping the public
  C++-natural `Γ → Γ` surface;
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

  /-- Branch merge for `if cond then s else t`.

  The condition is checked as a `CppCond`, producing a post-condition type
  environment `Γc`.  Both branches are checked from `Γc` and must expose the same
  control channel and exit environment. -/
  | ite
      {k : ControlKind} {Γ Γc Δ : TypeEnv}
      {cond : CppCond} {s t : CppStmt} :
      Micro.ConditionStatic Γ cond Γc →
      StmtTyping k Γc s Δ →
      StmtTyping k Γc t Δ →
      StmtTyping k Γ (.ite cond s t) Δ

  /-- Static while-normal route.

  The condition exposes the body-checking environment `Γc`; normal/break/continue
  body channels return to the outer loop environment `Γ`.  Runtime
  backedge/reentry safety is intentionally not asserted here. -/
  | whileNormal
      {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt} :
      Micro.ConditionStatic Γ cond Γc →
      StmtTyping .normalK Γc body Γ →
      StmtTyping .breakK Γc body Γ →
      StmtTyping .continueK Γc body Γ →
      StmtTyping .normalK Γ (.whileStmt cond body) Γ

  /-- Static while-return route. -/
  | whileReturn
      {Γ Γc Δ : TypeEnv} {cond : CppCond} {body : CppStmt} :
      Micro.ConditionStatic Γ cond Γc →
      StmtTyping .normalK Γc body Γ →
      StmtTyping .breakK Γc body Γ →
      StmtTyping .continueK Γc body Γ →
      StmtTyping .returnK Γc body Δ →
      StmtTyping .returnK Γ (.whileStmt cond body) Δ

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
