import CppFormalization.Cpp2.Core.TypeEnv
import CppFormalization.Cpp2.Core.Syntax

/-!
Expression typing.
-/

namespace Cpp

mutual

inductive HasPlaceType : TypeEnv → PlaceExpr → CppType → Prop where
  | var {Γ x d} :
      lookupDecl Γ x = some d →
      HasPlaceType Γ (.var x) (declPlaceType d)
  | deref {Γ e τ} :
      HasValueType Γ e (.ptr τ) →
      HasPlaceType Γ (.deref e) τ

inductive HasValueType : TypeEnv → ValExpr → CppType → Prop where
  | litBool {Γ b} : HasValueType Γ (.litBool b) (.base .bool)
  | litInt  {Γ n} : HasValueType Γ (.litInt n) (.base .int)
  | load    {Γ p τ} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.load p) τ
  | addrOf  {Γ p τ} :
      HasPlaceType Γ p τ →
      HasValueType Γ (.addrOf p) (.ptr τ)
  | add     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.add e₁ e₂) (.base .int)
  | sub     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.sub e₁ e₂) (.base .int)
  | mul     {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.mul e₁ e₂) (.base .int)
  | eq      {Γ e₁ e₂ τ} :
      HasValueType Γ e₁ τ →
      HasValueType Γ e₂ τ →
      HasValueType Γ (.eq e₁ e₂) (.base .bool)
  | lt      {Γ e₁ e₂} :
      HasValueType Γ e₁ (.base .int) →
      HasValueType Γ e₂ (.base .int) →
      HasValueType Γ (.lt e₁ e₂) (.base .bool)
  | not     {Γ e} :
      HasValueType Γ e (.base .bool) →
      HasValueType Γ (.not e) (.base .bool)
end

end Cpp
