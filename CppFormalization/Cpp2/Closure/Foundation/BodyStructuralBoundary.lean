import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Static.Safety.StateBoundary

namespace Cpp

/-!
# Closure.Foundation.BodyStructuralBoundary

Compatibility bridge for the old coarse `BodyReady` facade.

The pure structural boundary records now live in
`CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary`.

Only the old `BodyReady.toStructural` bridge remains here because `BodyReady`
belongs to `Static.Safety.StateBoundary`.
-/

def BodyReady.toStructural
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyReady Γ σ st) :
    BodyStructuralBoundary Γ st :=
  { wf := h.wf
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped }

end Cpp
