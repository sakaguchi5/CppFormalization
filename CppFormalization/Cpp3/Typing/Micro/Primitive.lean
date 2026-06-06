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

/-- Primitive declaration typing. -/
def decl
    {Γ Δ : TypeEnv} {d : CppDecl}
    (hform : DeclFormation Γ d) (henv : DeclEnvEffect Γ d Δ) :
    PrimitiveTyping Γ (.decl d) .normalK Δ where
  formation := PrimitiveFormation.decl hform
  control := PrimitiveControlEffect.decl
  env := PrimitiveEnvEffect.decl henv

/-- Primitive object declaration without an initializer typing. -/
def objectDeclNoInit
    {Γ : TypeEnv} {τ : CppType} {x : Ident}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ) :
    PrimitiveTyping Γ (.decl (.object τ x .noInit)) .normalK (declareTypeObject Γ x τ) where
  formation :=
    PrimitiveFormation.decl
      (DeclFormation.object hfresh hobj InitStatic.noInit)
  control := PrimitiveControlEffect.decl
  env := PrimitiveEnvEffect.decl DeclEnvEffect.object

/-- Primitive value-initialized object declaration typing. -/
def objectDeclValue
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {e : ValExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hobj : ObjectType τ)
    (he : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.decl (.object τ x (.value e))) .normalK (declareTypeObject Γ x τ) where
  formation :=
    PrimitiveFormation.decl
      (DeclFormation.object hfresh hobj (InitStatic.value he))
  control := PrimitiveControlEffect.decl
  env := PrimitiveEnvEffect.decl DeclEnvEffect.object

/-- Primitive reference declaration typing. -/
def refDecl
    {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr}
    (hfresh : currentTypeScopeFresh Γ x) (hp : HasPlaceType Γ p τ) :
    PrimitiveTyping Γ (.decl (.ref τ x p)) .normalK (declareTypeRef Γ x τ) where
  formation :=
    PrimitiveFormation.decl
      (DeclFormation.ref hfresh hp)
  control := PrimitiveControlEffect.decl
  env := PrimitiveEnvEffect.decl DeclEnvEffect.ref

/-- Primitive jump typing. -/
def jump
    {Γ : TypeEnv} {j : CppJump} {k : ControlKind}
    (hform : JumpFormation Γ j) (hctrl : JumpControlEffect j k) :
    PrimitiveTyping Γ (.jump j) k Γ where
  formation := PrimitiveFormation.jump hform
  control := PrimitiveControlEffect.jump hctrl
  env := PrimitiveEnvEffect.jump JumpEnvEffect.jump

/-- Primitive `break;` typing. -/
def breakStmt {Γ : TypeEnv} : PrimitiveTyping Γ (.jump .breakStmt) .breakK Γ where
  formation := PrimitiveFormation.jump JumpFormation.breakStmt
  control := PrimitiveControlEffect.jump JumpControlEffect.breakStmt
  env := PrimitiveEnvEffect.jump JumpEnvEffect.jump

/-- Primitive `continue;` typing. -/
def continueStmt {Γ : TypeEnv} : PrimitiveTyping Γ (.jump .continueStmt) .continueK Γ where
  formation := PrimitiveFormation.jump JumpFormation.continueStmt
  control := PrimitiveControlEffect.jump JumpControlEffect.continueStmt
  env := PrimitiveEnvEffect.jump JumpEnvEffect.jump

/-- Primitive `return;` typing. -/
def returnVoid {Γ : TypeEnv} :
    PrimitiveTyping Γ (.jump (.returnStmt .void)) .returnK Γ where
  formation :=
    PrimitiveFormation.jump
      (JumpFormation.returnStmt ReturnStatic.void)
  control := PrimitiveControlEffect.jump JumpControlEffect.returnStmt
  env := PrimitiveEnvEffect.jump JumpEnvEffect.jump

/-- Primitive `return e;` typing. -/
def returnValue
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType}
    (he : HasValueType Γ e τ) :
    PrimitiveTyping Γ (.jump (.returnStmt (.value e))) .returnK Γ where
  formation :=
    PrimitiveFormation.jump
      (JumpFormation.returnStmt (ReturnStatic.value he))
  control := PrimitiveControlEffect.jump JumpControlEffect.returnStmt
  env := PrimitiveEnvEffect.jump JumpEnvEffect.jump

end PrimitiveTyping

end Micro
end Typing
end Cpp3
