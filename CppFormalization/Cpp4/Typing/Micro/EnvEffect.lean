import CppFormalization.Cpp4.Core.TypeEnv

/-!
# CppFormalization.Cpp4.Typing.Micro.EnvEffect

Micro typing-level environment effects.

This is deliberately smaller than statement typing.  It records how a primitive
formation step changes the ordinary name environment, so later Judgment layers can
compose declarations, for-initializers, blocks, and scopes without rebuilding the
same environment vocabulary.
-/

namespace Cpp4

/-- A micro typing effect on the ordinary type environment. -/
inductive TypeEnvEffect : TypeEnv → TypeEnv → Type where
  /-- No ordinary-name environment change. -/
  | refl (Γ : TypeEnv) : TypeEnvEffect Γ Γ
  /-- Bind a fresh object name. -/
  | bindObject {Γ : TypeEnv} {x : Ident} {τ : CppType}
      (fresh : TypeEnv.Fresh Γ x) :
      TypeEnvEffect Γ (TypeEnv.bind Γ x (.object τ))
  /-- Bind a fresh reference name. -/
  | bindRef {Γ : TypeEnv} {x : Ident} {τ : CppType}
      (fresh : TypeEnv.Fresh Γ x) :
      TypeEnvEffect Γ (TypeEnv.bind Γ x (.ref τ))
  /-- Compose two adjacent micro environment effects. -/
  | trans {Γ Γ' Γ'' : TypeEnv}
      (left : TypeEnvEffect Γ Γ')
      (right : TypeEnvEffect Γ' Γ'') :
      TypeEnvEffect Γ Γ''

namespace TypeEnvEffect

/-- Alias for the identity environment effect. -/
def id (Γ : TypeEnv) : TypeEnvEffect Γ Γ :=
  .refl Γ

/-- Compose two micro environment effects. -/
def compose {Γ Γ' Γ'' : TypeEnv}
    (left : TypeEnvEffect Γ Γ')
    (right : TypeEnvEffect Γ' Γ'') :
    TypeEnvEffect Γ Γ'' :=
  .trans left right

end TypeEnvEffect

/-- A packaged environment effect with its post-environment.  This is convenient
for syntax-directed layers where the target environment is produced by typing. -/
structure TypedEnvEffect (Γ : TypeEnv) : Type where
  target : TypeEnv
  effect : TypeEnvEffect Γ target

namespace TypedEnvEffect

/-- Pack an unchanged environment. -/
def same (Γ : TypeEnv) : TypedEnvEffect Γ where
  target := Γ
  effect := TypeEnvEffect.id Γ

/-- Pack an object-name binding. -/
def bindObject {Γ : TypeEnv} {x : Ident} {τ : CppType}
    (fresh : TypeEnv.Fresh Γ x) : TypedEnvEffect Γ where
  target := TypeEnv.bind Γ x (.object τ)
  effect := TypeEnvEffect.bindObject fresh

/-- Pack a reference-name binding. -/
def bindRef {Γ : TypeEnv} {x : Ident} {τ : CppType}
    (fresh : TypeEnv.Fresh Γ x) : TypedEnvEffect Γ where
  target := TypeEnv.bind Γ x (.ref τ)
  effect := TypeEnvEffect.bindRef fresh

end TypedEnvEffect

end Cpp4
