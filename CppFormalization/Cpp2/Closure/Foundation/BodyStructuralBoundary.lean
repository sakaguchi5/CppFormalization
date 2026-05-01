import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp

/-!
# Closure.Foundation.BodyStructuralBoundary

Purely structural admission layer.

Redesign:
- `typed0` is removed from the structural layer.
- structural data now means only:
  * well-formedness,
  * top-level scopedness discipline.
- CI/static typing payloads move to `BodyStaticBoundaryCI`.
-/

structure BodyStructuralBoundary (Γ : TypeEnv) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st

structure BlockBodyStructuralBoundary (Γ : TypeEnv) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss

def BodyReady.toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReady Γ σ st) :
    BodyStructuralBoundary Γ st :=
  { wf := h.wf
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

end Cpp
