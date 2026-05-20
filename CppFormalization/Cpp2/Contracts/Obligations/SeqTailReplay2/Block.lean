import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Value

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: block replay

A block tail opens a fresh type/runtime scope.  Therefore block replay is kept
separate from statement replay at the route's current environment.
-/

/--
Replay for a block tail under the pushed block scope induced by the selected
route's post-environment and post-state.

The `cons` head is intentionally stated as ordinary pushed-scope statement
readiness.  A later block-specific route theory can replace that input by a
separate pushed-scope replay predicate without changing the statement-level API.
-/
inductive BlockReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    StmtBlock → Prop where
  | nil :
      BlockReplay route .nil
  | cons
      {st : CppStmt} {ss : StmtBlock} :
      StmtReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) st →
      BlockReplay route ss →
      BlockReplay route (.cons st ss)

namespace BlockReplay

/-- Block replay materializes concrete block readiness in the pushed scope. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {ss : StmtBlock}
    (h : BlockReplay route ss) :
    BlockReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) ss := by
  induction h with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hst _hss ih =>
      exact BlockReadyConcrete.cons hst ih

end BlockReplay

end SeqTailReplay2
end Cpp
