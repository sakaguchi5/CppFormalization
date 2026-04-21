import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Internal.AssignTransportKernel

`assign` の transport debt を一箇所へ束ねる。

設計方針:
- `Assigns` はそのまま operational relation として使う。
- write effect 自体は certificate structure ではなく、まず Prop-valued な
  logical boundary `AssignWriteEffect` として切り出す。
- read-side transport と expr-side transport は数学的に性質が違うので、
  kernel も `AssignReadTransportKernel` / `AssignExprTransportKernel` に分ける。
- ただし downstream 互換のため、旧 aggregate 名 `AssignTransportKernel` も残す。
-/


/-- Logical write-effect boundary exposed by an assignment step. -/
def AssignWriteEffect
    (σ σ' : State) (p : PlaceExpr) (v : Value) : Prop :=
  ∃ a c,
    BigStepPlace σ p a ∧
    σ.heap a = some c ∧
    c.alive = true ∧
    σ' = writeHeap σ a { c with value := some v }

/-- `Assigns` already packages exactly the data needed for the logical write effect. -/
theorem assignWriteEffect_of_Assigns
    {σ σ' : State} {p : PlaceExpr} {v : Value} :
    Assigns σ p v σ' →
    AssignWriteEffect σ σ' p v := by
  intro hassign
  rcases hassign with ⟨a, c, hplace, hheap, halive, _hcompat, rfl⟩
  exact ⟨a, c, hplace, hheap, halive, rfl⟩


/--
Read-places whose readiness is intended to be transportable across an
assignment step without committing to arbitrary alias-sensitive replay.
Current honest base keeps only variable places.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)


/-- Read-side transport facts used by the current mainline. -/
structure AssignReadTransportKernel : Type where
  selfPlace_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      PlaceReadyConcrete Γ σ p τ →
      BigStepStmt σ (.assign p e) .normal σ' →
      PlaceReadyConcrete Γ σ' p τ

  stableReadPlace_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ReplayStableReadPlace p →
      ScopedTypedStateConcrete Γ σ' →
      PlaceReadyConcrete Γ σ p τ →
      BigStepStmt σ (.assign q e) .normal σ' →
      PlaceReadyConcrete Γ σ' p τ

  stableLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ReplayStableReadPlace p →
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q e) .normal σ' →
      (∃ a, BigStepPlace σ' p a ∧ CellReadableTyped σ' a τ)


/--
Expr-side replay is intentionally separated from read-side transport.

理由:
- read-side transport は「どの観測者が assignment をまたいで保存されるか」という
  lower effect/kernel の問題である。
- expr replay は alias / footprint の影響を受けやすく、一般にはより強い負債である。
-/
structure AssignExprTransportKernel : Type where
  selfExpr_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType},
      HasValueType Γ e τ →
      ScopedTypedStateConcrete Γ σ' →
      ExprReadyConcrete Γ σ e τ →
      BigStepStmt σ (.assign p e) .normal σ' →
      ExprReadyConcrete Γ σ' e τ


/--
Backward-compatible aggregate package.

新設計では read / expr を分けて見るが、旧 surface を壊しすぎないために
aggregate wrapper も残しておく。
-/
structure AssignTransportKernel : Type where
  readKernel : AssignReadTransportKernel
  exprKernel : AssignExprTransportKernel


/--
Current primitive transport package.

重要:
- `AssignWriteEffect` は theorem-backed に `Assigns` から取り出せる。
- ただし readiness transport そのものは、まだ current shell debt として
  bundled kernel に残しておく。
-/
axiom assignTransportKernel : AssignTransportKernel


/-- Current read-side transport package. -/
noncomputable def assignReadTransportKernel : AssignReadTransportKernel :=
  assignTransportKernel.readKernel

/-- Current expr-side transport package. -/
noncomputable def assignExprTransportKernel : AssignExprTransportKernel :=
  assignTransportKernel.exprKernel


theorem assign_place_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ (.assign p e) .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro hσ' hpready hstep
  exact assignReadTransportKernel.selfPlace_after_assign hσ' hpready hstep


theorem assign_expr_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ e τ →
    BigStepStmt σ (.assign p e) .normal σ' →
    ExprReadyConcrete Γ σ' e τ := by
  intro hty hσ' heready hstep
  exact assignExprTransportKernel.selfExpr_after_assign hty hσ' heready hstep


theorem replay_stable_read_place_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {p q : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ (.assign q e) .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro hpstable hσ' hpready hstep
  exact assignReadTransportKernel.stableReadPlace_after_assign
    hpstable hσ' hpready hstep


theorem replay_stable_load_readable_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {p q : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q e) .normal σ' →
    (∃ a, BigStepPlace σ' p a ∧ CellReadableTyped σ' a τ) := by
  intro hpstable hσ' hread hstep
  exact assignReadTransportKernel.stableLoadReadable_after_assign
    hpstable hσ' hread hstep

end Cpp
