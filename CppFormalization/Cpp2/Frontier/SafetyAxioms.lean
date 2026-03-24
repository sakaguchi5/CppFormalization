import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Static.Inversions

/-!
Explicit semantic frontier.
These are the remaining non-constructive interfaces above the concrete core.
-/

namespace Cpp

axiom assigns_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {v : Value} {τ : CppType} :
    TypedState Γ σ →
    HasPlaceType Γ p τ →
    Assigns σ p v σ' →
    TypedState Γ σ'

axiom declares_object_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    TypedState Γ σ →
    DeclaresObject σ τ x ov σ' →
    TypedState (declareTypeObject Γ x τ) σ'

axiom declares_ref_preserves_typed_state
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    TypedState Γ σ →
    DeclaresRef σ τ x a σ' →
    TypedState (declareTypeRef Γ x τ) σ'

axiom place_progress
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    HasPlaceType Γ p τ →
    TypedState Γ σ →
    NoUninitPlace σ p →
    NoInvalidRefPlace σ p →
    ∃ a, BigStepPlace σ p a

axiom value_progress
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    TypedState Γ σ →
    NoUninitValue σ e →
    NoInvalidRefValue σ e →
    ∃ v, BigStepValue σ e v

axiom bigstep_preserves_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult} :
    HasTypeStmt Γ st Δ →
    TypedState Γ σ →
    BigStepStmt σ st ctrl σ' →
    TypedState Δ σ'

axiom stmt_safe_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    IdealAssumptions Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st

axiom no_uninit_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoUninitStmt σ st ↔ NoUninitStmt σ' st

axiom no_invalid_ref_state_irrel
    {σ σ' : State} {st : CppStmt} :
    NoInvalidRefStmt σ st ↔ NoInvalidRefStmt σ' st
/-
axiom no_top_break_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    BreakWellScoped st → BigStepStmt σ st .breakResult σ' → False

axiom no_top_continue_from_scope
    {σ : State} {st : CppStmt} {σ' : State} :
    ContinueWellScoped st → BigStepStmt σ st .continueResult σ' → False
-/
theorem ideal_no_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  exact stmt_safe_progress_or_diverges hfrag hassm

theorem ideal_no_unclassified_stuck
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hassm : IdealAssumptions Γ σ st) :
    ¬ UnclassifiedStuck σ st := by
  intro hstk
  rcases ideal_no_stuck (Γ := Γ) (σ := σ) (st := st) hfrag hassm with hterm | hdiv
  · exact hstk.1 hterm
  · exact hstk.2 hdiv

end Cpp
