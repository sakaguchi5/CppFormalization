import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteReadyTransport

`StateInvariantConcreteStrengthening` の ready package を、既存の ownership transport 定理へ
そのまま差し込める形にした接着層。

今回の責務は限定的である:
- `topFrameBindingFresh` / `nextNotTargetOfInnerRefs` を theorem ごとに直書きしない。
- 既存の transport 定理を `DeclareObjectReadyStrong` から呼べるようにする。
- まだ full `ScopedTypedStateConcreteOwnership` の assembly までは行かない。

これにより次段階では、side condition の散在を止めたまま、
object/ref declaration 後の ownership bundle を組み立てられる。
-/

namespace DeclareObjectReadyStrong

/-- object 宣言で必要な二つの side condition を reusable theorem として渡す。 -/
theorem objectSideConditions
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    topFrameBindingFresh σ x ∧ nextNotTargetOfInnerRefs σ :=
  h.sideConditions hΓ0

/-- object 宣言後，新旧すべての object binding は owned である。 -/
theorem objectsOwned_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {τ : CppType} {ov : Option Value} :
    allObjectBindingsOwned (declareObjectState σ τ x ov) := by
  exact allObjectBindingsOwned_declareObjectState
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.objectsOwned

/-- name-side package から，owned address の naming を object 宣言後へ transport する。 -/
theorem ownedNamed_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    allOwnedAddressesNamed (declareObjectState σ τ x ov) := by
  exact allOwnedAddressesNamed_declareObjectState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.ownedNamed
    (h.topFrameFresh hΓ0)

/-- name-side package から，ref-not-owned を object 宣言後へ transport する。 -/
theorem refsNotOwned_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    refBindingsNeverOwned (declareObjectState σ τ x ov) := by
  exact refBindingsNeverOwned_declareObjectState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.ownedNamed
    (h.topFrameFresh hΓ0)

/-- address-side package から，inner-owned 回避を object 宣言後へ transport する。 -/
theorem refTargetsAvoidInnerOwned_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {τ : CppType} {ov : Option Value} :
    ∀ {k : Nat} {y : Ident} {υ : CppType} {a : Nat} {j : Nat},
      runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareObjectState σ τ x ov) j a := by
  exact refTargetsAvoidInnerOwned_declareObjectState_of_noInnerNextAlias
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.refTargetsAvoidInnerOwned
    h.noInnerNextAlias

/-- object 宣言後の next-freshness は cursor successor の fresh 性から供給する。 -/
theorem nextFresh_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (_h : DeclareObjectReadyStrong Γ σ x)
    {τ : CppType} {ov : Option Value}
    (hnextSucc : freshAddrAgainstOwned σ (σ.next + 1)) :
    nextFreshAgainstOwned (declareObjectState σ τ x ov) := by
  exact nextFreshAgainstOwned_declareObjectState_of_freshSucc
    (σ := σ) (τ := τ) (x := x) (ov := ov) hnextSucc

/-- object 宣言後の per-frame no-dup は base concrete invariant から供給する。 -/
theorem ownedNoDup_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {τ : CppType} {ov : Option Value} :
    ownedAddressesNoDupPerFrame (declareObjectState σ τ x ov) := by
  exact ownedAddressesNoDupPerFrame_declareObjectState_of_nextFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov)
    h.concrete.ownedNoDupPerFrame
    h.concrete.nextFresh

end DeclareObjectReadyStrong

namespace DeclareRefReadyStrong

/-- ref 宣言については，name-side readiness だけ使えばよい。 -/
def Ready (Γ : TypeEnv) (σ : State) (x : Ident) : Prop :=
  DeclareObjectReadyStrong Γ σ x

/-- ref 宣言で使う top-frame freshness を object-ready package から流用する。 -/
theorem topFrameFresh
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    topFrameBindingFresh σ x := by
  exact h.topFrameFresh hΓ0

/-- ref 宣言後，object binding の ownership は保存される。 -/
theorem objectsOwned_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {τ : CppType} {a : Nat} :
    allObjectBindingsOwned (declareRefState σ τ x a) := by
  exact allObjectBindingsOwned_declareRefState
    (σ := σ) (τ := τ) (x := x) (a := a)
    h.concrete.objectsOwned

/-- ref 宣言後の owned-address naming。 -/
theorem ownedNamed_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat} :
    allOwnedAddressesNamed (declareRefState σ τ x a) := by
  exact allOwnedAddressesNamed_declareRefState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a)
    h.concrete.ownedNamed
    (h.topFrameFresh hΓ0)

/-- ref 宣言後の ref-not-owned。 -/
theorem refsNotOwned_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat} :
    refBindingsNeverOwned (declareRefState σ τ x a) := by
  exact refBindingsNeverOwned_declareRefState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a)
    h.concrete.ownedNamed
    (h.topFrameFresh hΓ0)

/-- ref 宣言後も inner-owned 回避はそのまま保存される。 -/
theorem refTargetsAvoidInnerOwned_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {τ : CppType} {a : Nat} :
    ∀ {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} {j : Nat},
      runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareRefState σ τ x a) j addr := by
  exact refTargetsAvoidInnerOwned_declareRefState
    (σ := σ) (τ := τ) (x := x) (r := a)
    h.concrete.refTargetsAvoidInnerOwned

/-- ref 宣言後も next-freshness は保存される。 -/
theorem nextFresh_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {τ : CppType} {a : Nat} :
    nextFreshAgainstOwned (declareRefState σ τ x a) := by
  rcases h.concrete.nextFresh with ⟨hheap, hlocals⟩
  refine ⟨?_, ?_⟩
  · simpa [declareRefState] using hheap
  · intro k fr hk
    cases hsc : σ.scopes with
    | nil =>
        cases k with
        | zero =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          -- fr.locals は [] なので、σ.next ∈ [] は偽になる
          simp [declareRefState]
        | succ k => simp [declareRefState, scopes_bindTopBinding, hsc] at hk
    | cons fr0 frs =>
        cases k with
        | zero =>
            -- 1. fr = fr0 であることを導出（localsが不変であることを示すため）
            rcases declareRefState_lookup_zero_frame_of_cons
              (σ := σ) (τ := τ) (x := x) (a := a)
              (fr0 := fr0) (frs := frs) hsc hk with rfl
            -- 2. ゴールは ¬(declareRefState σ τ x a).next ∈ fr0.locals
            -- declareRefState は next を変えないので、simp で整理
            simp [declareRefState]
            -- 3. 元の freshness 前提を使用
            exact hlocals 0 fr0 (by simp [hsc])
        | succ k =>
            -- 1. k.succ 番目のフレームは元の scopes の k.succ 番目と同じ
            have hk_old : σ.scopes[k.succ]? = some fr := by
              simpa [declareRefState, hsc] using hk
            -- 2. simp で next を整理してから適用
            simp [declareRefState]
            exact hlocals k.succ fr hk_old

/-- ref 宣言後も per-frame no-dup は保存される。 -/
theorem ownedNoDup_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {τ : CppType} {a : Nat} :
    ownedAddressesNoDupPerFrame (declareRefState σ τ x a) := by
  exact (ownedAddressesNoDupPerFrame_declareRefState
    (σ := σ) (τ := τ) (x := x) (a := a)).2 h.concrete.ownedNoDupPerFrame

/-- ref 宣言後も frame 間 disjointness は保存される。 -/
theorem ownedDisjoint_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {τ : CppType} {a : Nat} :
    ownedAddressesDisjointAcrossFrames (declareRefState σ τ x a) := by
  exact (ownedAddressesDisjointAcrossFrames_declareRefState
    (σ := σ) (τ := τ) (x := x) (a := a)).2 h.concrete.ownedDisjoint

end DeclareRefReadyStrong

end Cpp
