import CppFormalization.Cpp2.Core.TypeEnv

/-!
Primitive type-environment frame query predicates.
-/

namespace Cpp

def typeFrameDeclObject (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.object τ)

def typeFrameDeclRef (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.ref τ)

end Cpp
