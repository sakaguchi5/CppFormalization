import CppFormalization.Cpp2.Semantics.Expr
import CppFormalization.Cpp2.Typing.Stmt
import CppFormalization.Cpp2.Static.WellFormed
import CppFormalization.Cpp2.Static.ScopeDiscipline
import CppFormalization.Cpp2.Core.RuntimeState

/-!
Safety predicates and ideal boundary assumptions.
-/

namespace Cpp

def ValidPlace (σ : State) (p : PlaceExpr) : Prop :=
  ∃ a c, BigStepPlace σ p a ∧ σ.heap a = some c ∧ c.alive = true

def ReadablePlace (σ : State) (p : PlaceExpr) : Prop :=
  ∃ a c v, BigStepPlace σ p a ∧ σ.heap a = some c ∧ c.alive = true ∧ c.value = some v

def NoUninitPlace (σ : State) (p : PlaceExpr) : Prop :=
  ValidPlace σ p

def NoUninitValue (σ : State) : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => ReadablePlace σ p
  | .addrOf p => ValidPlace σ p
  | .add e₁ e₂ => NoUninitValue σ e₁ ∧ NoUninitValue σ e₂
  | .sub e₁ e₂ => NoUninitValue σ e₁ ∧ NoUninitValue σ e₂
  | .mul e₁ e₂ => NoUninitValue σ e₁ ∧ NoUninitValue σ e₂
  | .eq e₁ e₂ => NoUninitValue σ e₁ ∧ NoUninitValue σ e₂
  | .lt e₁ e₂ => NoUninitValue σ e₁ ∧ NoUninitValue σ e₂
  | .not e => NoUninitValue σ e

mutual

def NoUninitStmt (σ : State) : CppStmt → Prop
  | .skip => True
  | .exprStmt e => NoUninitValue σ e
  | .assign p e => NoUninitPlace σ p ∧ NoUninitValue σ e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => NoUninitValue σ e
  | .declareRef _ _ p => NoUninitPlace σ p
  | .seq s t => NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .ite c s t => NoUninitValue σ c ∧ NoUninitStmt σ s ∧ NoUninitStmt σ t
  | .whileStmt c b => NoUninitValue σ c ∧ NoUninitStmt σ b
  | .block ss => NoUninitBlock σ ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => NoUninitValue σ e

def NoUninitBlock (σ : State) : StmtBlock → Prop
  | .nil => True
  | .cons s ss => NoUninitStmt σ s ∧ NoUninitBlock σ ss

end

def NoInvalidRefPlace (σ : State) (p : PlaceExpr) : Prop :=
  ValidPlace σ p

def NoInvalidRefValue (σ : State) : ValExpr → Prop
  | .litBool _ => True
  | .litInt _ => True
  | .load p => ValidPlace σ p
  | .addrOf p => ValidPlace σ p
  | .add e₁ e₂ => NoInvalidRefValue σ e₁ ∧ NoInvalidRefValue σ e₂
  | .sub e₁ e₂ => NoInvalidRefValue σ e₁ ∧ NoInvalidRefValue σ e₂
  | .mul e₁ e₂ => NoInvalidRefValue σ e₁ ∧ NoInvalidRefValue σ e₂
  | .eq e₁ e₂ => NoInvalidRefValue σ e₁ ∧ NoInvalidRefValue σ e₂
  | .lt e₁ e₂ => NoInvalidRefValue σ e₁ ∧ NoInvalidRefValue σ e₂
  | .not e => NoInvalidRefValue σ e

mutual

def NoInvalidRefStmt (σ : State) : CppStmt → Prop
  | .skip => True
  | .exprStmt e => NoInvalidRefValue σ e
  | .assign p e => NoInvalidRefPlace σ p ∧ NoInvalidRefValue σ e
  | .declareObj _ _ none => True
  | .declareObj _ _ (some e) => NoInvalidRefValue σ e
  | .declareRef _ _ p => NoInvalidRefPlace σ p
  | .seq s t => NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .ite c s t => NoInvalidRefValue σ c ∧ NoInvalidRefStmt σ s ∧ NoInvalidRefStmt σ t
  | .whileStmt c b => NoInvalidRefValue σ c ∧ NoInvalidRefStmt σ b
  | .block ss => NoInvalidRefBlock σ ss
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt none => True
  | .returnStmt (some e) => NoInvalidRefValue σ e

def NoInvalidRefBlock (σ : State) : StmtBlock → Prop
  | .nil => True
  | .cons s ss => NoInvalidRefStmt σ s ∧ NoInvalidRefBlock σ ss

end


def DeclMatchesBinding : DeclInfo → Binding → Prop
  | .object τ, .object τ' _ => τ = τ'
  | .ref τ, .ref τ' _ => τ = τ'
  | _, _ => False


def TypedState (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x d,
    lookupDecl Γ x = some d →
    ∃ b c,
      lookupBinding σ x = some b ∧
      DeclMatchesBinding d b ∧
      σ.heap (bindingAddr b) = some c ∧
      c.ty = declPlaceType d ∧
      c.alive = true


def IdealAssumptions (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellFormedStmt st ∧
  WellTypedFrom Γ st ∧
  TypedState Γ σ ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st ∧
  BreakWellScoped st ∧
  ContinueWellScoped st

end Cpp
