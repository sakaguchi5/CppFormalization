import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Place

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: value-expression replay

`ValueReplay route e τ` says that a value expression used by the tail is ready in
the selected post-state.  Pure expressions are constructor-backed.  Memory reads
and pointer-derived expressions carry the exact post-state witnesses needed by
C++ safety.
-/

/--
Route-local replay for value expressions used by the tail.

This is intentionally integrated from the start: there is no separate
"pure/load/deref/full" stage.  The inductive follows the semantic constructors
of value-expression readiness.
-/
inductive ValueReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | litBool {b : Bool} :
      ValueReplay route (.litBool b) (.base .bool)
  | litInt {n : Int} :
      ValueReplay route (.litInt n) (.base .int)
  | load
      {p : PlaceExpr} {τ : CppType} :
      PlaceReplay route p τ →
      (∃ a, BigStepPlace σ1 p a ∧ CellReadableTyped σ1 a τ) →
      ValueReplay route (.load p) τ
  | addrOf
      {p : PlaceExpr} {τ : CppType} :
      PlaceReplay route p τ →
      ValueReplay route (.addrOf p) (.ptr τ)
  | add
      {e₁ e₂ : ValExpr} :
      ValueReplay route e₁ (.base .int) →
      ValueReplay route e₂ (.base .int) →
      ValueReplay route (.add e₁ e₂) (.base .int)
  | sub
      {e₁ e₂ : ValExpr} :
      ValueReplay route e₁ (.base .int) →
      ValueReplay route e₂ (.base .int) →
      ValueReplay route (.sub e₁ e₂) (.base .int)
  | mul
      {e₁ e₂ : ValExpr} :
      ValueReplay route e₁ (.base .int) →
      ValueReplay route e₂ (.base .int) →
      ValueReplay route (.mul e₁ e₂) (.base .int)
  | eq
      {e₁ e₂ : ValExpr} {τ : CppType} :
      ValueReplay route e₁ τ →
      ValueReplay route e₂ τ →
      ValueReplay route (.eq e₁ e₂) (.base .bool)
  | lt
      {e₁ e₂ : ValExpr} :
      ValueReplay route e₁ (.base .int) →
      ValueReplay route e₂ (.base .int) →
      ValueReplay route (.lt e₁ e₂) (.base .bool)
  | not
      {e : ValExpr} :
      ValueReplay route e (.base .bool) →
      ValueReplay route (.not e) (.base .bool)

namespace ValueReplay

/-- Value replay gives static value typing. -/
theorem hasValueType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : ValueReplay route e τ) :
    HasValueType route.Θ e τ := by
  induction h with
  | litBool =>
      exact HasValueType.litBool
  | litInt =>
      exact HasValueType.litInt
  | load hplace _hread =>
      exact HasValueType.load hplace.hasPlaceType
  | addrOf hplace =>
      exact HasValueType.addrOf hplace.hasPlaceType
  | add _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.add ih₁ ih₂
  | sub _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.sub ih₁ ih₂
  | mul _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.mul ih₁ ih₂
  | eq _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.eq ih₁ ih₂
  | lt _h₁ _h₂ ih₁ ih₂ =>
      exact HasValueType.lt ih₁ ih₂
  | not _h ih =>
      exact HasValueType.not ih

/-- Value replay gives concrete post-state expression readiness. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : ValueReplay route e τ) :
    ExprReadyConcrete route.Θ σ1 e τ := by
  induction h with
  | litBool =>
      exact ExprReadyConcrete.litBool
  | litInt =>
      exact ExprReadyConcrete.litInt
  | load hplace hread =>
      exact ExprReadyConcrete.load hplace.ready hread
  | addrOf hplace =>
      exact ExprReadyConcrete.addrOf hplace.ready
  | add _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.add ih₁ ih₂
  | sub _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.sub ih₁ ih₂
  | mul _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.mul ih₁ ih₂
  | eq _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.eq ih₁ ih₂
  | lt _h₁ _h₂ ih₁ ih₂ =>
      exact ExprReadyConcrete.lt ih₁ ih₂
  | not _h ih =>
      exact ExprReadyConcrete.not ih

end ValueReplay

end SeqTailReplay2
end Cpp
