import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteReadyTransport
import CppFormalization.Cpp2.Closure.Foundation.Readiness

namespace Cpp

/-!
# Closure.Foundation.DeclareReadyStrongBridge

`DeclareObjectReadyStrong` / `DeclareRefReadyStrong` を、
既存の

- `ScopedTypedStateConcrete`
- `ScopedTypedStateConcreteStrengthening`
- `currentTypeScopeFresh`

から組み立てる薄い bridge 層。

重要:
- ここでは operational axiom 自体はまだ消さない。
- ただし strong route の hidden hypothesis のうち
  `currentTypeFrameFresh` への持ち上げは theorem 化する。
- さらに `StmtReadyConcrete` の declare-object / declare-ref case から
  strong-ready package を直接取り出せるようにする。

これで次段階では、
`declareRef_stmt_normal_data_strong` の「強さ」のうち
ready package 構成部分を axiom から外へ出せる。
-/

/-- top-scope freshness を frame-quantified freshness へ持ち上げる。 -/
theorem currentTypeFrameFresh_of_currentTypeScopeFresh
    {Γ : TypeEnv} {x : Ident} :
    currentTypeScopeFresh Γ x →
    currentTypeFrameFresh Γ x := by
  intro hfresh Γfr hΓ0
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr frs =>
      have hEq : Γfr = fr := by
        simpa [hsc] using hΓ0.symm
      subst hEq
      simpa [currentTypeScopeFresh, hsc] using hfresh

/-- concrete + strengthening + scope freshness から object-ready package を組む。 -/
theorem declareObjectReadyStrong_of_scopeFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcreteStrengthening Γ σ →
    currentTypeScopeFresh Γ x →
    DeclareObjectReadyStrong Γ σ x := by
  intro hconcrete hstrength hfresh
  exact
    { concrete := hconcrete
      strengthening := hstrength
      typeFresh := currentTypeFrameFresh_of_currentTypeScopeFresh hfresh }

/-- ref 版は object-ready package の別名。 -/
theorem declareRefReadyStrong_of_scopeFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcreteStrengthening Γ σ →
    currentTypeScopeFresh Γ x →
    DeclareRefReadyStrong.Ready Γ σ x := by
  intro hconcrete hstrength hfresh
  exact declareObjectReadyStrong_of_scopeFresh hconcrete hstrength hfresh

/-- `declareObj` ready から strong-ready package を抽出する。 -/
theorem declareObjectReadyStrong_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} {oe : Option ValExpr} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcreteStrengthening Γ σ →
    StmtReadyConcrete Γ σ (.declareObj τ x oe) →
    DeclareObjectReadyStrong Γ σ x := by
  intro hconcrete hstrength hready
  cases hready with
  | declareObjNone hfresh _ =>
      exact declareObjectReadyStrong_of_scopeFresh hconcrete hstrength hfresh
  | declareObjSome hfresh _ _ _ =>
      exact declareObjectReadyStrong_of_scopeFresh hconcrete hstrength hfresh

/-- `declareRef` ready から strong-ready package を抽出する。 -/
theorem declareRefReadyStrong_of_stmtReadyConcrete
    {Γ : TypeEnv} {σ : State} {τ : CppType} {x : Ident} {p : PlaceExpr} :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcreteStrengthening Γ σ →
    StmtReadyConcrete Γ σ (.declareRef τ x p) →
    DeclareRefReadyStrong.Ready Γ σ x := by
  intro hconcrete hstrength hready
  cases hready with
  | declareRef hfresh _ _ =>
      exact declareRefReadyStrong_of_scopeFresh hconcrete hstrength hfresh

end Cpp
