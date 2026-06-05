import CppFormalization.Cpp3.Typing.Micro.Primitive
import CppFormalization.Cpp3.Contracts.Core.Assumption
import CppFormalization.Cpp3.Contracts.Core.Kind

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.NormalBindStatic

Static normal-bind component for statement sequencing.

This is the static half of `s; t`: if the head can finish normally with an
intermediate type environment, the tail is checked from that environment.  It
contains no post-state continuation contract yet.
-/

/-- Static normal-bind data for `seq s t`, parameterized by the judgment that
will later be reconstructed from micro components. -/
structure NormalBindStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Θ Δ : TypeEnv) (s t : CppStmt) : Prop where
  headNormal : J .normalK Γ s Θ
  tail       : J k Θ t Δ

namespace NormalBindStatic

/-- Project certified head-normal evidence from a normal-bind component. -/
def certifiedHead
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
    (h : NormalBindStatic J k Γ Θ Δ s t) :
    Contracts.Certified (J .normalK Γ s Θ) :=
  h.headNormal

/-- Project certified tail evidence from a normal-bind component. -/
def certifiedTail
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
    (h : NormalBindStatic J k Γ Θ Δ s t) :
    Contracts.Certified (J k Θ t Δ) :=
  h.tail

end NormalBindStatic

end Composition
end Micro
end Typing
end Cpp3
