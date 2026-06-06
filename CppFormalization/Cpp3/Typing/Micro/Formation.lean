import CppFormalization.Cpp3.Core.All

namespace Cpp3
namespace Typing
namespace Micro

/-!
# CppFormalization.Cpp3.Typing.Micro.Formation

The first micro layer: local syntactic/static formation.

This file deliberately stops before composition.  It says when primitive
expressions, control conditions, declaration initializers, declarations, returns,
jumps, assignments, and primitive statements are locally well-formed in a type
environment, but it does not say how `seq`, `cons`, `block`, `ite`, or `while`
compose.
-/

mutual

/-- Type of a place expression in a type environment. -/
inductive HasPlaceType : TypeEnv → PlaceExpr → CppType → Prop where
  | var
      {Γ : TypeEnv} {x : Ident} {d : DeclInfo} :
      lookupDecl Γ x = some d →
      HasPlaceType Γ (.var x) (declPlaceType d)

  | deref
      {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
      HasValueType Γ e (.ptr τ) →
      HasPlaceType Γ (.deref e) τ

/-- Type of a value expression in a type environment. -/
inductive HasValueType : TypeEnv → ValExpr → CppType → Prop where
  | litBool
      {Γ : TypeEnv} {b : Bool} :
      HasValueType Γ (.litBool b) (.base .bool)

  | litInt
      {Γ : TypeEnv} {n : Int} :
      HasValueType Γ (.litInt n) (.base .int)

  | load
      {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.load p) τ

  | addrOf
      {Γ : TypeEnv} {p : PlaceExpr} {τ : CppType} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.addrOf p) (.ptr τ)

  | add
      {Γ : TypeEnv} {a b : ValExpr} :
      HasValueType Γ a (.base .int) →
      HasValueType Γ b (.base .int) →
      HasValueType Γ (.add a b) (.base .int)

  | sub
      {Γ : TypeEnv} {a b : ValExpr} :
      HasValueType Γ a (.base .int) →
      HasValueType Γ b (.base .int) →
      HasValueType Γ (.sub a b) (.base .int)

  | mul
      {Γ : TypeEnv} {a b : ValExpr} :
      HasValueType Γ a (.base .int) →
      HasValueType Γ b (.base .int) →
      HasValueType Γ (.mul a b) (.base .int)

  | eq
      {Γ : TypeEnv} {a b : ValExpr} {τ : CppType} :
      HasValueType Γ a τ →
      HasValueType Γ b τ →
      HasValueType Γ (.eq a b) (.base .bool)

  | lt
      {Γ : TypeEnv} {a b : ValExpr} :
      HasValueType Γ a (.base .int) →
      HasValueType Γ b (.base .int) →
      HasValueType Γ (.lt a b) (.base .bool)

  | not
      {Γ : TypeEnv} {e : ValExpr} :
      HasValueType Γ e (.base .bool) →
      HasValueType Γ (.not e) (.base .bool)

end

/-- Static typing/effect surface of a C++ condition clause.

`ConditionStatic Γ cond Γc` says that condition `cond`, checked from `Γ`,
produces a boolean control result and exposes the post-condition type
environment `Γc`.

For the current expression-only condition core, `Γc = Γ`.  The environment index
is intentional: later C++ condition declarations can extend this judgment
without redesigning `if` and `while`. -/
inductive ConditionStatic : TypeEnv → CppCond → TypeEnv → Prop where
  | expr
      {Γ : TypeEnv} {e : ValExpr} :
      HasValueType Γ e (.base .bool) →
      ConditionStatic Γ (.expr e) Γ

namespace ConditionStatic

/-- Current expression-only conditions do not change the type environment. -/
def exprSameEnv
    {Γ : TypeEnv} {e : ValExpr}
    (h : HasValueType Γ e (.base .bool)) :
    ConditionStatic Γ (.expr e) Γ :=
  .expr h

end ConditionStatic

/-- Static formation of an object initializer.

The initializer is a separate syntax category because it is the point where
value evaluation, storage compatibility, and declaration lifetime meet. -/
inductive InitStatic : TypeEnv → CppType → CppInit → Prop where
  | noInit
      {Γ : TypeEnv} {τ : CppType} :
      InitStatic Γ τ .noInit

  | value
      {Γ : TypeEnv} {τ : CppType} {e : ValExpr} :
      HasValueType Γ e τ →
      InitStatic Γ τ (.value e)

/-- Static formation of a C++ declaration. -/
inductive DeclFormation : TypeEnv → CppDecl → Prop where
  | object
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {init : CppInit} :
      currentTypeScopeFresh Γ x →
      ObjectType τ →
      InitStatic Γ τ init →
      DeclFormation Γ (.object τ x init)

  | ref
      {Γ : TypeEnv} {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh Γ x →
      HasPlaceType Γ p τ →
      DeclFormation Γ (.ref τ x p)

/-- Static formation of a return payload. -/
inductive ReturnStatic : TypeEnv → CppReturn → Prop where
  | void
      {Γ : TypeEnv} :
      ReturnStatic Γ .void

  | value
      {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
      HasValueType Γ e τ →
      ReturnStatic Γ (.value e)

/-- Static formation of a C++ jump. -/
inductive JumpFormation : TypeEnv → CppJump → Prop where
  | breakStmt
      {Γ : TypeEnv} :
      JumpFormation Γ .breakStmt

  | continueStmt
      {Γ : TypeEnv} :
      JumpFormation Γ .continueStmt

  | returnStmt
      {Γ : TypeEnv} {r : CppReturn} :
      ReturnStatic Γ r →
      JumpFormation Γ (.returnStmt r)

/-- Static formation of a C++ assignment. -/
inductive AssignFormation : TypeEnv → CppAssign → Prop where
  | simple
      {Γ : TypeEnv} {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      HasPlaceType Γ p τ →
      HasValueType Γ e τ →
      AssignFormation Γ (.simple p e)

/-- Primitive statement formation.

This layer has no tail/continuation contract.  For example, simple assignment is
locally formed when its place and value have matching types; whether that
assignment keeps a later tail safe belongs to a later obligation slot. -/
inductive PrimitiveFormation : TypeEnv → CppStmt → Prop where
  | skip
      {Γ : TypeEnv} :
      PrimitiveFormation Γ .skip

  | exprStmt
      {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
      HasValueType Γ e τ →
      PrimitiveFormation Γ (.exprStmt e)

  | assign
      {Γ : TypeEnv} {a : CppAssign} :
      AssignFormation Γ a →
      PrimitiveFormation Γ (.assign a)

  | decl
      {Γ : TypeEnv} {d : CppDecl} :
      DeclFormation Γ d →
      PrimitiveFormation Γ (.decl d)

  | jump
      {Γ : TypeEnv} {j : CppJump} :
      JumpFormation Γ j →
      PrimitiveFormation Γ (.jump j)

end Micro
end Typing
end Cpp3
