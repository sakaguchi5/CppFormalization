import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp

/-!
# Closure.Foundation.BodyStructuralBoundary

四層分離の第1層。

ここでは state に依存しない structural admission だけを切り出す。
old `BodyReady` が抱えていた
- well-formedness
- old coarse typing
- top-level scopedness
を、dynamic / CI adequacy から分離して固定する。
-/

/-- State-independent structural boundary for a top-level function body. -/
structure BodyStructuralBoundary (Γ : TypeEnv) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed0 : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st

/--
State-independent structural boundary for an opened block body.

block body は `pushTypeScope Γ` 下で読むが、
この層では dynamic state はまだ入れない。
-/
structure BlockBodyStructuralBoundary (Γ : TypeEnv) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed0 : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss

/-- Forget the old `BodyReady` dynamic fields and recover the structural layer. -/
def BodyReady.toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReady Γ σ st) :
    BodyStructuralBoundary Γ st :=
  { wf := h.wf
    typed0 := h.typed
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

end Cpp
