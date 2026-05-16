import CppFormalization.Cpp2.Effects.NameEffect
import CppFormalization.Cpp2.Effects.HeapEffect
import CppFormalization.Cpp2.Effects.ReadEffect

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.NormalHeadEffect

Axiom-free combined effect certificates for primitive normal heads.

This is intentionally not a Closure boundary.  It is a proof-side ledger saying:
when a primitive head finishes normally, what happened to names, heap, and fresh
read/addressability facts.

Because the operational semantics is `Prop`, the constructor from a normal step
is stated propositionally as `Nonempty ...` rather than as a data-returning
function.
-/

/-- Combined effect certificate for one primitive normal head. -/
inductive NormalHeadEffect
    (Γ Δ : TypeEnv) (σ σ' : State) : CppStmt → Type where
  | skip :
      EnvPreservingEffect Γ Δ .skip →
      HeapUnchanged σ σ' →
      NormalHeadEffect Γ Δ σ σ' .skip
  | exprStmt {e : ValExpr} :
      EnvPreservingEffect Γ Δ (.exprStmt e) →
      HeapUnchanged σ σ' →
      NormalHeadEffect Γ Δ σ σ' (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      EnvPreservingEffect Γ Δ (.assign p e) →
      AssignHeapWriteEffect σ σ' p e →
      NormalHeadEffect Γ Δ σ σ' (.assign p e)
  | declareObjNone {τ : CppType} {x : Ident} :
      DeclareObjNameEffect Γ Δ τ x →
      ObjectDeclHeapIntroEffect σ σ' τ x none →
      NormalHeadEffect Γ Δ σ σ' (.declareObj τ x none)
  | declareObjSome {τ : CppType} {x : Ident} {e : ValExpr} {v : Value} :
      DeclareObjNameEffect Γ Δ τ x →
      HasValueType Γ e τ →
      BigStepValue σ e v →
      ObjectDeclHeapIntroEffect σ σ' τ x (some v) →
      NormalHeadEffect Γ Δ σ σ' (.declareObj τ x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} {a : Nat} :
      DeclareRefNameEffect Γ Δ τ x p →
      BigStepPlace σ p a →
      RefDeclBindingEffect σ σ' τ x a →
      NormalHeadEffect Γ Δ σ σ' (.declareRef τ x p)

/--
Existentially build the combined effect certificate for a primitive normal head.

This is intentionally a theorem into `Prop`, not a `def` returning a certificate:
`BigStepStmt` is `Prop`, and extracting concrete witnesses from it into `Type`
would require noncomputable choice.  `Nonempty` is enough for proof work and
remains axiom-free.
-/
theorem nonempty_normalHeadEffect_of_ctx
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (hprim : PrimitiveNormalHead head)
    (hctx : NormalHeadCtx Γ Δ σ σ' head) :
    Nonempty (NormalHeadEffect Γ Δ σ σ' head) := by
  cases hprim with
  | skip =>
      exact ⟨NormalHeadEffect.skip
        (envPreservingEffect_of_skip_typing hctx.typing)
        (heapUnchanged_of_skip_step hctx.step)⟩
  | exprStmt =>
      exact ⟨NormalHeadEffect.exprStmt
        (envPreservingEffect_of_exprStmt_typing hctx.typing)
        (heapUnchanged_of_exprStmt_step hctx.step)⟩
  | assign =>
      rcases nonempty_assignHeapWriteEffect_of_step hctx.step with ⟨hw⟩
      exact ⟨NormalHeadEffect.assign
        (envPreservingEffect_of_assign_typing hctx.typing)
        hw⟩
  | declareObjNone =>
      rcases nonempty_objectDeclHeapIntroEffect_of_none_step hctx.step with ⟨heff⟩
      exact ⟨NormalHeadEffect.declareObjNone
        (declareObjNameEffect_of_none_typing hctx.typing)
        heff⟩
  | declareObjSome =>
      rcases declareObjSome_post_env_data hctx.typing with
        ⟨_hfresh, _hobj, htyInit, _hΔ⟩
      rcases exists_objectDeclHeapIntroEffect_of_some_step hctx.step with
        ⟨v, hval, heffExists⟩
      rcases heffExists with ⟨heff⟩
      exact ⟨NormalHeadEffect.declareObjSome
        (v := v)
        (declareObjNameEffect_of_some_typing hctx.typing)
        htyInit
        hval
        heff⟩
  | declareRef =>
      rcases refDeclBindingEffect_of_step hctx.step with ⟨a, hplace, href⟩
      exact ⟨NormalHeadEffect.declareRef
        (a := a)
        (declareRefNameEffect_of_typing hctx.typing)
        hplace
        href⟩

namespace NormalHeadEffect

/-- Extract the name effect from a combined normal-head effect. -/
def nameEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (h : NormalHeadEffect Γ Δ σ σ' head) :
    NormalHeadNameEffect Γ Δ head := by
  cases h with
  | skip hname _ => exact .skip hname
  | exprStmt hname _ => exact .exprStmt hname
  | assign hname _ => exact .assign hname
  | declareObjNone hname _ => exact .declareObjNone hname
  | declareObjSome hname hty _ _ => exact .declareObjSome hname hty
  | declareRef hname _ _ => exact .declareRef hname

end NormalHeadEffect

end Cpp
