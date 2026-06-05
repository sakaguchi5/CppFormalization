import CppFormalization.Cpp3.Typing.Micro.EnvEffect
import CppFormalization.Cpp3.Contracts.Core.Assumption
import CppFormalization.Cpp3.Contracts.Core.Kind

namespace Cpp3
namespace Typing
namespace Micro

/-!
# CppFormalization.Cpp3.Typing.Micro.Primitive

Primitive typing is the product of three local micro components:
formation, control effect, and type-environment effect.
-/

/-- Primitive statement typing, before any compound composition. -/
structure PrimitiveTyping
    (Γ : TypeEnv) (st : CppStmt) (k : ControlKind) (Δ : TypeEnv) : Prop where
  formation : PrimitiveFormation Γ st
  control   : PrimitiveControlEffect st k
  env       : PrimitiveEnvEffect Γ st Δ

namespace PrimitiveTyping

/-- The formation component is certified by a primitive typing package. -/
def certifiedFormation
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (h : PrimitiveTyping Γ st k Δ) :
    Contracts.Certified (PrimitiveFormation Γ st) :=
  h.formation

/-- The control-effect component is certified by a primitive typing package. -/
def certifiedControl
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (h : PrimitiveTyping Γ st k Δ) :
    Contracts.Certified (PrimitiveControlEffect st k) :=
  h.control

/-- The environment-effect component is certified by a primitive typing package. -/
def certifiedEnv
    {Γ : TypeEnv} {st : CppStmt} {k : ControlKind} {Δ : TypeEnv}
    (h : PrimitiveTyping Γ st k Δ) :
    Contracts.Certified (PrimitiveEnvEffect Γ st Δ) :=
  h.env

/-- Primitive `skip` typing. -/
def skip {Γ : TypeEnv} : PrimitiveTyping Γ .skip .normalK Γ where
  formation := PrimitiveFormation.skip
  control := PrimitiveControlEffect.skip
  env := PrimitiveEnvEffect.skip

/-- Primitive expression-statement typing. -/
def exprStmt
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType}
    (h : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.exprStmt e) .normalK Γ where
  formation := PrimitiveFormation.exprStmt h
  control := PrimitiveControlEffect.exprStmt
  env := PrimitiveEnvEffect.exprStmt

/-- Primitive assignment typing. -/
def assign
    {Γ : TypeEnv} {p : PlaceExpr} {e : ValExpr} {τ : CppType}
    (hp : HasPlaceType Γ p τ) (he : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.assign p e) .normalK Γ where
  formation := PrimitiveFormation.assign hp he
  control := PrimitiveControlEffect.assign
  env := PrimitiveEnvEffect.assign

/-- Primitive uninitialized object declaration typing. -/
def declareObjNone
    {Γ : TypeEnv} {τ : CppType} {x : Ident}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ) :
    PrimitiveTyping Γ (.declareObj τ x none) .normalK (declareTypeObject Γ x τ) where
  formation := PrimitiveFormation.declareObjNone hfresh hobj
  control := PrimitiveControlEffect.declareObj
  env := PrimitiveEnvEffect.declareObj

/-- Primitive initialized object declaration typing. -/
def declareObjSome
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ)
    (he : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.declareObj τ x (some e)) .normalK (declareTypeObject Γ x τ) where
  formation := PrimitiveFormation.declareObjSome hfresh hobj he
  control := PrimitiveControlEffect.declareObj
  env := PrimitiveEnvEffect.declareObj

/-- Primitive reference declaration typing. -/
def declareRef
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hp : HasPlaceType Γ p τ) :
    PrimitiveTyping Γ (.declareRef τ x p) .normalK (declareTypeRef Γ x τ) where
  formation := PrimitiveFormation.declareRef hfresh hp
  control := PrimitiveControlEffect.declareRef
  env := PrimitiveEnvEffect.declareRef

/-- Primitive `break` typing. -/
def breakStmt {Γ : TypeEnv} : PrimitiveTyping Γ .breakStmt .breakK Γ where
  formation := PrimitiveFormation.breakStmt
  control := PrimitiveControlEffect.breakStmt
  env := PrimitiveEnvEffect.breakStmt

/-- Primitive `continue` typing. -/
def continueStmt {Γ : TypeEnv} : PrimitiveTyping Γ .continueStmt .continueK Γ where
  formation := PrimitiveFormation.continueStmt
  control := PrimitiveControlEffect.continueStmt
  env := PrimitiveEnvEffect.continueStmt

/-- Primitive `return;` typing. -/
def returnNone {Γ : TypeEnv} : PrimitiveTyping Γ (.returnStmt none) .returnK Γ where
  formation := PrimitiveFormation.returnNone
  control := PrimitiveControlEffect.returnStmt
  env := PrimitiveEnvEffect.returnStmt

/-- Primitive `return e;` typing. -/
def returnSome
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType}
    (he : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.returnStmt (some e)) .returnK Γ where
  formation := PrimitiveFormation.returnSome he
  control := PrimitiveControlEffect.returnStmt
  env := PrimitiveEnvEffect.returnStmt

end PrimitiveTyping

end Micro
end Typing
end Cpp3
