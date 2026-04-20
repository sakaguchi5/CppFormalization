import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedDerefTheorems

namespace Cpp

/-!
Condition replay extended by the fully theoremized strong thin-separated deref
witness family.

`ConditionReplayKernel` deliberately excluded dereference-based condition
fragments. After theoremizing the separation-side local interface for
`addrOf`/`load`, we can now add back the honest deref-based part that is
supported by those witnesses.

This file is intentionally assignment-centered:
the new witness family is about replay across a specific head assignment
`q := rhs`.
-/


/- =========================================================
   1. Assignment-centered deref-aware condition fragment
   ========================================================= -/

/--
Condition/value-expression fragment replayable across a *specific* head
assignment `q := rhs`.

This extends the old `ReplayStableCondExpr` with the two deref-based source
forms now supported by `StrongThinSeparatedWitness`:
- `load (.deref e)`
- `addrOf (.deref e)`

Everything else is built compositionally on top of that.
-/
inductive StrongThinSeparatedCondExpr
    (Γ : TypeEnv) (σ : State) (q : PlaceExpr) (rhs : ValExpr) :
    ValExpr → CppType → Prop where
  | base {e : ValExpr} {τ : CppType} :
      ReplayStableCondExpr e →
      HasValueType Γ e τ →
      StrongThinSeparatedCondExpr Γ σ q rhs e τ

  | loadDeref {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedWitness Γ σ q rhs e τ →
      StrongThinSeparatedCondExpr Γ σ q rhs (.load (.deref e)) τ

  | addrOfDeref {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedWitness Γ σ q rhs e τ →
      StrongThinSeparatedCondExpr Γ σ q rhs (.addrOf (.deref e)) (.ptr τ)

  | add {e₁ e₂ : ValExpr} :
      StrongThinSeparatedCondExpr Γ σ q rhs e₁ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs e₂ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs (.add e₁ e₂) (.base .int)

  | sub {e₁ e₂ : ValExpr} :
      StrongThinSeparatedCondExpr Γ σ q rhs e₁ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs e₂ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs (.sub e₁ e₂) (.base .int)

  | mul {e₁ e₂ : ValExpr} :
      StrongThinSeparatedCondExpr Γ σ q rhs e₁ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs e₂ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs (.mul e₁ e₂) (.base .int)

  | eq {e₁ e₂ : ValExpr} {τ : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e₁ τ →
      StrongThinSeparatedCondExpr Γ σ q rhs e₂ τ →
      StrongThinSeparatedCondExpr Γ σ q rhs (.eq e₁ e₂) (.base .bool)

  | lt {e₁ e₂ : ValExpr} :
      StrongThinSeparatedCondExpr Γ σ q rhs e₁ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs e₂ (.base .int) →
      StrongThinSeparatedCondExpr Γ σ q rhs (.lt e₁ e₂) (.base .bool)

  | not {e : ValExpr} :
      StrongThinSeparatedCondExpr Γ σ q rhs e (.base .bool) →
      StrongThinSeparatedCondExpr Γ σ q rhs (.not e) (.base .bool)

@[simp] theorem StrongThinSeparatedWitness.hasPtrType
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    StrongThinSeparatedWitness Γ σ q rhs e τ →
    HasValueType Γ e (.ptr τ) := by
  intro w
  exact w.toThin.ptrType

@[simp] theorem hasPlaceType_deref_of_hasValueType_ptr
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e (.ptr τ) →
    HasPlaceType Γ (.deref e) τ := by
  intro h
  exact HasPlaceType.deref h

@[simp] theorem StrongThinSeparatedCondExpr.hasValueType
    {Γ σ q rhs e τ} :
    StrongThinSeparatedCondExpr Γ σ q rhs e τ →
    HasValueType Γ e τ := by
  intro h
  induction h with
  | base _ hty =>
      exact hty
  | loadDeref hw =>
      exact HasValueType.load <|
        hasPlaceType_deref_of_hasValueType_ptr hw.hasPtrType
  | addrOfDeref hw =>
      exact HasValueType.addrOf <|
        hasPlaceType_deref_of_hasValueType_ptr hw.hasPtrType
  | add _ _ ih₁ ih₂ =>
      exact HasValueType.add ih₁ ih₂
  | sub _ _ ih₁ ih₂ =>
      exact HasValueType.sub ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
      exact HasValueType.mul ih₁ ih₂
  | eq _ _ ih₁ ih₂ =>
      exact HasValueType.eq ih₁ ih₂
  | lt _ _ ih₁ ih₂ =>
      exact HasValueType.lt ih₁ ih₂
  | not _ ih =>
      exact HasValueType.not ih

@[simp] theorem PlaceReadyConcrete.hasPlaceType
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} :
    PlaceReadyConcrete Γ σ p τ →
    HasPlaceType Γ p τ :=
  hasPlaceType_of_placeReadyConcrete

@[simp] theorem ExprReadyConcrete.hasValueType
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType} :
    ExprReadyConcrete Γ σ e τ →
    HasValueType Γ e τ :=
  hasValueType_of_exprReadyConcrete

/- =========================================================
   2. Replay theorem across the head assignment
   ========================================================= -/

theorem strongThinSeparated_cond_expr_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {τ : CppType} :
    StrongThinSeparatedCondExpr Γ σ q rhs c τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ c τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' c τ := by
  intro hc hσ' hready hstep
  induction hc generalizing σ' with
  | base hbase hty =>
      exact replay_stable_cond_expr_ready_after_assign hbase hσ' hready hstep

  | loadDeref hw =>
      cases hready with
      | load hpready hread =>
          exact ExprReadyConcrete.load
            (deref_place_ready_after_assign_of_strongThinSeparatedWitness
              hw hσ' hpready hstep)
            (deref_load_readable_after_assign_of_strongThinSeparatedWitness
              hw hσ' hread hstep)

  | addrOfDeref hw =>
      cases hready with
      | addrOf hpready =>
          exact ExprReadyConcrete.addrOf
            (deref_place_ready_after_assign_of_strongThinSeparatedWitness
              hw hσ' hpready hstep)

  | add hc₁ hc₂ ih₁ ih₂ =>
      cases hready with
      | add hready₁ hready₂ =>
          exact ExprReadyConcrete.add
            (ih₁ hσ' hready₁ hstep)
            (ih₂ hσ' hready₂ hstep)

  | sub hc₁ hc₂ ih₁ ih₂ =>
      cases hready with
      | sub hready₁ hready₂ =>
          exact ExprReadyConcrete.sub
            (ih₁ hσ' hready₁ hstep)
            (ih₂ hσ' hready₂ hstep)

  | mul hc₁ hc₂ ih₁ ih₂ =>
      cases hready with
      | mul hready₁ hready₂ =>
          exact ExprReadyConcrete.mul
            (ih₁ hσ' hready₁ hstep)
            (ih₂ hσ' hready₂ hstep)

  | eq hc₁ hc₂ ih₁ ih₂ =>
      cases hready with
      | eq hready₁ hready₂ =>
          -- hready₁ の持つ型（自動生成された型変数）を、hc₁ の型（τ）と一致させる
          have heq1 := hasValueType_unique hready₁.hasValueType hc₁.hasValueType
          subst heq1
          exact ExprReadyConcrete.eq (ih₁ hσ' hready₁ hstep) (ih₂ hσ' hready₂ hstep)

  | lt hc₁ hc₂ ih₁ ih₂ =>
      cases hready with
      | lt hready₁ hready₂ =>
          exact ExprReadyConcrete.lt
            (ih₁ hσ' hready₁ hstep)
            (ih₂ hσ' hready₂ hstep)

  | not hc ih =>
      cases hready with
      | not hready' =>
          exact ExprReadyConcrete.not
            (ih hσ' hready' hstep)


/- =========================================================
   3. Useful specializations for the two deref source forms
   ========================================================= -/

theorem load_deref_expr_ready_after_assign_of_addrOfThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ (.load (.deref (.addrOf p))) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' (.load (.deref (.addrOf p))) τ := by
  intro w hσ' hready hstep
  exact strongThinSeparated_cond_expr_ready_after_assign
    (StrongThinSeparatedCondExpr.loadDeref
      (StrongThinSeparatedWitness.ofAddrOf w))
    hσ' hready hstep

theorem load_deref_expr_ready_after_assign_of_loadThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ (.load (.deref (.load p))) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' (.load (.deref (.load p))) τ := by
  intro w hσ' hready hstep
  exact strongThinSeparated_cond_expr_ready_after_assign
    (StrongThinSeparatedCondExpr.loadDeref
      (StrongThinSeparatedWitness.ofLoad w))
    hσ' hready hstep

theorem addrof_deref_expr_ready_after_assign_of_addrOfThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs (.addrOf p) τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ (.addrOf (.deref (.addrOf p))) (.ptr τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' (.addrOf (.deref (.addrOf p))) (.ptr τ) := by
  intro w hσ' hready hstep
  exact strongThinSeparated_cond_expr_ready_after_assign
    (StrongThinSeparatedCondExpr.addrOfDeref
      (StrongThinSeparatedWitness.ofAddrOf w))
    hσ' hready hstep

theorem addrof_deref_expr_ready_after_assign_of_loadThinSeparatedWitness
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ (.addrOf (.deref (.load p))) (.ptr τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' (.addrOf (.deref (.load p))) (.ptr τ) := by
  intro w hσ' hready hstep
  exact strongThinSeparated_cond_expr_ready_after_assign
    (StrongThinSeparatedCondExpr.addrOfDeref
      (StrongThinSeparatedWitness.ofLoad w))
    hσ' hready hstep

end Cpp
