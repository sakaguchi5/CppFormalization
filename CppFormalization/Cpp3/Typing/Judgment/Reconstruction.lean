import CppFormalization.Cpp3.Typing.Judgment.Stmt

namespace Cpp3
namespace Typing
namespace Judgment

/-!
# CppFormalization.Cpp3.Typing.Judgment.Reconstruction

Smart constructors from micro components into the public Cpp3 typing judgment.

This file is deliberately one-way: it shows how the visible typing judgment is
assembled from micro components.  Later inversion/provenance files can provide
the opposite direction where useful.
-/

namespace StmtTyping

/-- Reconstruct statement typing from a primitive micro package. -/
def ofPrimitive
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (h : Micro.PrimitiveTyping Γ st k Δ) :
    StmtTyping k Γ st Δ :=
  StmtTyping.primitive h

/-- Reconstruct `seq` typing from a static normal-bind component. -/
def ofNormalBindStatic
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
    (embed : ∀ {k Γ st Δ}, J k Γ st Δ → StmtTyping k Γ st Δ)
    (h : Micro.Composition.NormalBindStatic J k Γ Θ Δ s t) :
    StmtTyping k Γ (.seq s t) Δ :=
  StmtTyping.seqNormal
    (embed h.headNormal)
    (embed h.tail)

/-- Specialized reconstruction when the component is already parameterized by
`StmtTyping`. -/
def ofNormalBind
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {s t : CppStmt}
    (h : Micro.Composition.NormalBindStatic StmtTyping k Γ Θ Δ s t) :
    StmtTyping k Γ (.seq s t) Δ :=
  StmtTyping.seqNormal h.headNormal h.tail

/-- Reconstruct abrupt `seq` typing from a static short-circuit component. -/
def ofAbruptShortCircuitStatic
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt}
    (embed : ∀ {k Γ st Δ}, J k Γ st Δ → StmtTyping k Γ st Δ)
    (h : Micro.Composition.AbruptShortCircuitStatic J k Γ Δ s t) :
    StmtTyping k Γ (.seq s t) Δ :=
  StmtTyping.seqAbrupt h.abrupt (embed h.head)

/-- Specialized reconstruction when the component is already parameterized by
`StmtTyping`. -/
def ofAbruptShortCircuit
    {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt}
    (h : Micro.Composition.AbruptShortCircuitStatic StmtTyping k Γ Δ s t) :
    StmtTyping k Γ (.seq s t) Δ :=
  StmtTyping.seqAbrupt h.abrupt h.head

/-- Primitive `skip`. -/
def skip {Γ : TypeEnv} : StmtTyping .normalK Γ .skip Γ :=
  ofPrimitive Micro.PrimitiveTyping.skip

/-- Primitive expression statement. -/
def exprStmt
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType}
    (h : Micro.HasValueType Γ e τ) :
    StmtTyping .normalK Γ (.exprStmt e) Γ :=
  ofPrimitive (Micro.PrimitiveTyping.exprStmt h)

/-- Primitive assignment. -/
def assign
    {Γ : TypeEnv} {p : PlaceExpr} {e : ValExpr} {τ : CppType}
    (hp : Micro.HasPlaceType Γ p τ) (he : Micro.HasValueType Γ e τ) :
    StmtTyping .normalK Γ (.assign p e) Γ :=
  ofPrimitive (Micro.PrimitiveTyping.assign hp he)

/-- Primitive uninitialized object declaration. -/
def declareObjNone
    {Γ : TypeEnv} {τ : CppType} {x : Ident}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ) :
    StmtTyping .normalK Γ (.declareObj τ x none) (declareTypeObject Γ x τ) :=
  ofPrimitive (Micro.PrimitiveTyping.declareObjNone hfresh hobj)

/-- Primitive initialized object declaration. -/
def declareObjSome
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ)
    (he : Micro.HasValueType Γ e τ) :
    StmtTyping .normalK Γ (.declareObj τ x (some e)) (declareTypeObject Γ x τ) :=
  ofPrimitive (Micro.PrimitiveTyping.declareObjSome hfresh hobj he)

/-- Primitive reference declaration. -/
def declareRef
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hp : Micro.HasPlaceType Γ p τ) :
    StmtTyping .normalK Γ (.declareRef τ x p) (declareTypeRef Γ x τ) :=
  ofPrimitive (Micro.PrimitiveTyping.declareRef hfresh hp)

/-- Primitive `break;`. -/
def breakStmt {Γ : TypeEnv} : StmtTyping .breakK Γ .breakStmt Γ :=
  ofPrimitive Micro.PrimitiveTyping.breakStmt

/-- Primitive `continue;`. -/
def continueStmt {Γ : TypeEnv} : StmtTyping .continueK Γ .continueStmt Γ :=
  ofPrimitive Micro.PrimitiveTyping.continueStmt

/-- Primitive `return;`. -/
def returnNone {Γ : TypeEnv} : StmtTyping .returnK Γ (.returnStmt none) Γ :=
  ofPrimitive Micro.PrimitiveTyping.returnNone

/-- Primitive `return e;`. -/
def returnSome
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType}
    (he : Micro.HasValueType Γ e τ) :
    StmtTyping .returnK Γ (.returnStmt (some e)) Γ :=
  ofPrimitive (Micro.PrimitiveTyping.returnSome he)

end StmtTyping

namespace BlockTyping

/-- Empty block body. -/
def empty {Γ : TypeEnv} : BlockTyping .normalK Γ .nil Γ :=
  BlockTyping.nil

/-- Reconstruct block-cons typing from a static normal block-cons component. -/
def ofBlockConsNormalStatic
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {JBlock : ControlKind → TypeEnv → StmtBlock → TypeEnv → Prop}
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (embedStmt : ∀ {k Γ st Δ}, JStmt k Γ st Δ → StmtTyping k Γ st Δ)
    (embedBlock : ∀ {k Γ ss Δ}, JBlock k Γ ss Δ → BlockTyping k Γ ss Δ)
    (h : Micro.Composition.BlockConsNormalStatic JStmt JBlock k Γ Θ Δ head tail) :
    BlockTyping k Γ (.cons head tail) Δ :=
  BlockTyping.consNormal
    (embedStmt h.headNormal)
    (embedBlock h.tailTyping)

/-- Specialized reconstruction when the component is already parameterized by
`StmtTyping` and `BlockTyping`. -/
def ofBlockConsNormal
    {k : ControlKind} {Γ Θ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : Micro.Composition.BlockConsNormalStatic StmtTyping BlockTyping k Γ Θ Δ head tail) :
    BlockTyping k Γ (.cons head tail) Δ :=
  BlockTyping.consNormal h.headNormal h.tailTyping

/-- Reconstruct abrupt block-cons typing from a static short-circuit component. -/
def ofBlockConsAbruptStatic
    {JStmt : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (embedStmt : ∀ {k Γ st Δ}, JStmt k Γ st Δ → StmtTyping k Γ st Δ)
    (h : Micro.Composition.BlockConsAbruptStatic JStmt k Γ Δ head tail) :
    BlockTyping k Γ (.cons head tail) Δ :=
  BlockTyping.consAbrupt h.abrupt (embedStmt h.headTyping)

/-- Specialized reconstruction when the component is already parameterized by
`StmtTyping`. -/
def ofBlockConsAbrupt
    {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : Micro.Composition.BlockConsAbruptStatic StmtTyping k Γ Δ head tail) :
    BlockTyping k Γ (.cons head tail) Δ :=
  BlockTyping.consAbrupt h.abrupt h.headTyping

end BlockTyping

end Judgment
end Typing
end Cpp3
