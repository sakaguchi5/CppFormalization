import CppFormalization.Cpp3.Typing.Micro.Composition.AbruptShortCircuitStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.BlockConsStatic

Static components for block-body cons.

These components are deliberately parameterized by the statement and block
judgments that will later be reconstructed.  They do not yet claim any runtime
continuation safety.
-/

/-- Static normal case for `StmtBlock.cons head tail`. -/
structure BlockConsNormalStatic
    (JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop)
    (k : ControlKind) (Γ Θ Δ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Prop where
  headNormal : JStmt .normalK Γ head Θ
  tailTyping : JBlock k Θ tail Δ

/-- Static abrupt case for `StmtBlock.cons head tail`. -/
structure BlockConsAbruptStatic
    (JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Δ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Prop where
  abrupt : AbruptKind k
  headTyping : JStmt k Γ head Δ

namespace BlockConsNormalStatic

/-- Project certified normal head evidence. -/
def certifiedHead
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockConsNormalStatic JStmt JBlock k Γ Θ Δ head tail) :
    Contracts.Certified (JStmt .normalK Γ head Θ) :=
  h.headNormal

/-- Project certified tail evidence. -/
def certifiedTail
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockConsNormalStatic JStmt JBlock k Γ Θ Δ head tail) :
    Contracts.Certified (JBlock k Θ tail Δ) :=
  h.tailTyping

end BlockConsNormalStatic

namespace BlockConsAbruptStatic

/-- Project certified abrupt-kind evidence. -/
def certifiedAbrupt
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockConsAbruptStatic JStmt k Γ Δ head tail) :
    Contracts.Certified (AbruptKind k) :=
  h.abrupt

/-- Project certified abrupt head evidence. -/
def certifiedHead
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockConsAbruptStatic JStmt k Γ Δ head tail) :
    Contracts.Certified (JStmt k Γ head Δ) :=
  h.headTyping

end BlockConsAbruptStatic

end Composition
end Micro
end Typing
end Cpp3
