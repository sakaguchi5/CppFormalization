import CppFormalization.Cpp2.Effect.NameEffect
import CppFormalization.Cpp2.Static.Env.TypeEnvQuery
import CppFormalization.Cpp2.RuntimeModel.RuntimeQuery
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.ReadEffect

Axiom-free read/addressability facts that belong to the effect layer.

This file reconstructs the useful fresh-name facts below `Closure`: a fresh
object/ref name is introduced from the post-state invariant, `addrOf` is ready
from place readiness, and `load` is ready only under an explicit
`CellReadableTyped` premise.
-/

/-! ## Top-frame declaration witnesses for fresh declarations -/

theorem typeFrameDeclObject_zero_declareTypeObject
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    typeFrameDeclObject (declareTypeObject Γ x τ) 0 x τ := by
  unfold typeFrameDeclObject declareTypeObject insertTopDecl
  cases Γ.scopes with
  | nil =>
      refine ⟨{ decls := fun y => if y = x then some (.object τ) else none }, ?_, ?_⟩
      · simp
      · simp
  | cons fr frs =>
      refine ⟨{ fr with decls := fun y => if y = x then some (.object τ) else fr.decls y }, ?_, ?_⟩
      · simp
      · simp

theorem typeFrameDeclRef_zero_declareTypeRef
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    typeFrameDeclRef (declareTypeRef Γ x τ) 0 x τ := by
  unfold typeFrameDeclRef declareTypeRef insertTopDecl
  cases Γ.scopes with
  | nil =>
      refine ⟨{ decls := fun y => if y = x then some (.ref τ) else none }, ?_, ?_⟩
      · simp
      · simp
  | cons fr frs =>
      refine ⟨{ fr with decls := fun y => if y = x then some (.ref τ) else fr.decls y }, ?_, ?_⟩
      · simp
      · simp

/-! ## Runtime top-frame binding lookup -/

theorem lookupBinding_of_runtimeFrameBindsObject_zero
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsObject σ 0 x τ a →
    lookupBinding σ x = some (.object τ a) := by
  intro h
  rcases h with ⟨fr, hscope, hbind⟩
  cases hσ : σ.scopes with
  | nil =>
      simp [hσ] at hscope
  | cons fr0 frs =>
      have hfr : fr0 = fr := by
        simpa [hσ] using hscope
      subst hfr
      simp [lookupBinding, lookupBindingFrames, hσ, hbind]

theorem lookupBinding_of_runtimeFrameBindsRef_zero
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsRef σ 0 x τ a →
    lookupBinding σ x = some (.ref τ a) := by
  intro h
  rcases h with ⟨fr, hscope, hbind⟩
  cases hσ : σ.scopes with
  | nil =>
      simp [hσ] at hscope
  | cons fr0 frs =>
      have hfr : fr0 = fr := by
        simpa [hσ] using hscope
      subst hfr
      simp [lookupBinding, lookupBindingFrames, hσ, hbind]

/-! ## Fresh place data and fresh place readiness -/

theorem declareObj_fresh_object_place_data_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ) :
    ∃ a,
      lookupBinding σ x = some (.object τ a) ∧
      BigStepPlace σ (.var x) a ∧
      CellLiveTyped σ a τ := by
  have htyDecl : typeFrameDeclObject (declareTypeObject Γ x τ) 0 x τ :=
    typeFrameDeclObject_zero_declareTypeObject
  rcases hpost.objectDeclRealized htyDecl with ⟨a, hbindObj, _hown, hlive⟩
  have hlookup : lookupBinding σ x = some (.object τ a) :=
    lookupBinding_of_runtimeFrameBindsObject_zero hbindObj
  exact ⟨a, hlookup, BigStepPlace.varObject hlookup, by simpa [CellLiveTyped, heapLiveTypedAt] using hlive⟩

theorem declareRef_fresh_place_data_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ) :
    ∃ a,
      lookupBinding σ x = some (.ref τ a) ∧
      BigStepPlace σ (.var x) a ∧
      CellLiveTyped σ a τ := by
  have htyDecl : typeFrameDeclRef (declareTypeRef Γ x τ) 0 x τ :=
    typeFrameDeclRef_zero_declareTypeRef
  rcases hpost.refDeclRealized htyDecl with ⟨a, hbindRef, hlive⟩
  have hlookup : lookupBinding σ x = some (.ref τ a) :=
    lookupBinding_of_runtimeFrameBindsRef_zero hbindRef
  exact ⟨a, hlookup, BigStepPlace.varRef hlookup, by simpa [CellLiveTyped, heapLiveTypedAt] using hlive⟩

theorem declareObj_fresh_object_place_ready_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ) :
    PlaceReadyConcrete (declareTypeObject Γ x τ) σ (.var x) τ := by
  rcases declareObj_fresh_object_place_data_of_post hpost with ⟨a, hlookup, _hplace, hlive⟩
  have hdecl : lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by simp
  exact PlaceReadyConcrete.varObject hdecl hlookup hlive

theorem declareRef_fresh_place_ready_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ) :
    PlaceReadyConcrete (declareTypeRef Γ x τ) σ (.var x) τ := by
  rcases declareRef_fresh_place_data_of_post hpost with ⟨a, hlookup, _hplace, hlive⟩
  have hdecl : lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by simp
  exact PlaceReadyConcrete.varRef hdecl hlookup hlive

/-! ## Load and addressability facts -/

theorem load_ready_of_place_and_readable
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} {a : Nat}
    (hp : PlaceReadyConcrete Γ σ p τ)
    (hplace : BigStepPlace σ p a)
    (hread : CellReadableTyped σ a τ) :
    ExprReadyConcrete Γ σ (.load p) τ := by
  exact ExprReadyConcrete.load hp ⟨a, hplace, hread⟩

theorem declareObj_fresh_object_load_ready_of_post_and_readable
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ)
    (hread : ∀ {a : Nat}, lookupBinding σ x = some (.object τ a) → CellReadableTyped σ a τ) :
    ExprReadyConcrete (declareTypeObject Γ x τ) σ (.load (.var x)) τ := by
  rcases declareObj_fresh_object_place_data_of_post hpost with ⟨a, hlookup, hplace, _hlive⟩
  have hp := declareObj_fresh_object_place_ready_of_post hpost
  exact load_ready_of_place_and_readable hp hplace (hread hlookup)

theorem declareRef_fresh_load_ready_of_post_and_readable
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ)
    (hread : ∀ {a : Nat}, lookupBinding σ x = some (.ref τ a) → CellReadableTyped σ a τ) :
    ExprReadyConcrete (declareTypeRef Γ x τ) σ (.load (.var x)) τ := by
  rcases declareRef_fresh_place_data_of_post hpost with ⟨a, hlookup, hplace, _hlive⟩
  have hp := declareRef_fresh_place_ready_of_post hpost
  exact load_ready_of_place_and_readable hp hplace (hread hlookup)

theorem declareObj_fresh_addrOf_ready_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ) :
    ExprReadyConcrete (declareTypeObject Γ x τ) σ (.addrOf (.var x)) (.ptr τ) := by
  exact ExprReadyConcrete.addrOf (declareObj_fresh_object_place_ready_of_post hpost)

theorem declareRef_fresh_addrOf_ready_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ) :
    ExprReadyConcrete (declareTypeRef Γ x τ) σ (.addrOf (.var x)) (.ptr τ) := by
  exact ExprReadyConcrete.addrOf (declareRef_fresh_place_ready_of_post hpost)

theorem declareObj_fresh_addrOf_ptr_value_ready_at_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ) :
    ∃ a, PtrValueReadyAt (declareTypeObject Γ x τ) σ (.addrOf (.var x)) τ a := by
  rcases declareObj_fresh_object_place_data_of_post hpost with ⟨a, _hlookup, hplace, _hlive⟩
  have hdecl : lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by simp
  have hpty : HasPlaceType (declareTypeObject Γ x τ) (.var x) τ := HasPlaceType.var hdecl
  exact ⟨a, ptrValueReadyAt_addrOf hpty hplace⟩

theorem declareRef_fresh_addrOf_ptr_value_ready_at_of_post
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident}
    (hpost : ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ) :
    ∃ a, PtrValueReadyAt (declareTypeRef Γ x τ) σ (.addrOf (.var x)) τ a := by
  rcases declareRef_fresh_place_data_of_post hpost with ⟨a, _hlookup, hplace, _hlive⟩
  have hdecl : lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by simp
  have hpty : HasPlaceType (declareTypeRef Γ x τ) (.var x) τ := HasPlaceType.var hdecl
  exact ⟨a, ptrValueReadyAt_addrOf hpty hplace⟩

end Cpp
