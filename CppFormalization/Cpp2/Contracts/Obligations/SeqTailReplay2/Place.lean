import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Basic

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: place replay

A place replay witness says that a tail place is valid in the selected
post-state.  This is the first genuinely C++-dependent layer: bindings,
references, dereference targets, and live typed cells can be destroyed by the
left statement, so they must be checked at the post-state.
-/

/--
Route-local replay for places used by the tail.

The `varObject` and `varRef` cases are ordinary name/binding replay.  The
`deref` case records the pointer value and live typed target cell needed for
`PlaceReadyConcrete.deref`.
-/
inductive PlaceReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    PlaceExpr → CppType → Prop where
  | varObject
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.object τ) →
      lookupBinding σ1 x = some (.object τ a) →
      CellLiveTyped σ1 a τ →
      PlaceReplay route (.var x) τ
  | varRef
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.ref τ) →
      lookupBinding σ1 x = some (.ref τ a) →
      CellLiveTyped σ1 a τ →
      PlaceReplay route (.var x) τ
  | deref
      {e : ValExpr} {τ : CppType} {a : Nat} :
      PtrValueReadyAt route.Θ σ1 e τ a →
      CellLiveTyped σ1 a τ →
      PlaceReplay route (.deref e) τ

namespace PlaceReplay

/-- Place replay gives the static place typing needed by readiness. -/
theorem hasPlaceType
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : PlaceReplay route p τ) :
    HasPlaceType route.Θ p τ := by
  cases h with
  | varObject hdecl _hbind _hlive =>
      exact HasPlaceType.var hdecl
  | varRef hdecl _hbind _hlive =>
      exact HasPlaceType.var hdecl
  | deref hptr _hlive =>
      exact HasPlaceType.deref hptr.1

/-- Place replay gives concrete post-state place readiness. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : PlaceReplay route p τ) :
    PlaceReadyConcrete route.Θ σ1 p τ := by
  cases h with
  | varObject hdecl hbind hlive =>
      exact PlaceReadyConcrete.varObject hdecl hbind hlive
  | varRef hdecl hbind hlive =>
      exact PlaceReadyConcrete.varRef hdecl hbind hlive
  | deref hptr hlive =>
      exact PlaceReadyConcrete.deref hptr hlive

end PlaceReplay

end SeqTailReplay2
end Cpp
