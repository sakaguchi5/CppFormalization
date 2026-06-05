import CppFormalization.Cpp3.Core.RuntimeState

/-!
Primitive matching vocabulary between static declarations and runtime bindings.
-/

namespace Cpp3

def DeclMatchesBinding : DeclInfo → Binding → Prop
  | .object τ, .object τ' _ => τ = τ'
  | .ref τ, .ref τ' _ => τ = τ'
  | _, _ => False

end Cpp3
