import CppFormalization.Cpp3.Typing.Micro.Composition.NormalBindStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.AbruptShortCircuitStatic

Static short-circuit component for compound statements.

If the head produces an abrupt channel, the tail is not statically consumed by
that channel.  This is the shared idea behind `seq_break`, `seq_continue`,
`seq_return`, and the corresponding block-cons cases.
-/

/-- Static abrupt short-circuit data for `seq s t`, parameterized by the final
statement judgment. -/
structure AbruptShortCircuitStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Δ : TypeEnv) (s t : CppStmt) : Prop where
  abrupt : AbruptKind k
  head   : J k Γ s Δ

namespace AbruptShortCircuitStatic

/-- Project certified abrupt-kind evidence. -/
def certifiedAbrupt
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt}
    (h : AbruptShortCircuitStatic J k Γ Δ s t) :
    Contracts.Certified (AbruptKind k) :=
  h.abrupt

/-- Project certified head evidence. -/
def certifiedHead
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt}
    (h : AbruptShortCircuitStatic J k Γ Δ s t) :
    Contracts.Certified (J k Γ s Δ) :=
  h.head

end AbruptShortCircuitStatic

end Composition
end Micro
end Typing
end Cpp3
