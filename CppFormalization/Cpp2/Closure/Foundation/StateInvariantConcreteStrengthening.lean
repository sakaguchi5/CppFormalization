import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteOwnershipTransport

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteStrengthening

中間解のための strengthening 層。

狙いは二つ:

1. `topFrameBindingFresh` を、宣言入力 `x` を本体 invariant に押し込まずに、
   `Γ` と `σ` の frame-local exact correspondence から導けるようにする。
2. `nextNotTargetOfInnerRefs` を、ad hoc な object-declaration 前提ではなく、
   runtime-global な ref-live invariant から導けるようにする。

設計方針:
- 名前の問題は `Γ` と `σ` の対応理論で解く。
- address / lifetime の問題は ref target の live 性で解く。
- そのうえで declaration-ready な support structure にまとめる。
-/

/--
1 個の type frame と 1 個の runtime frame が、名前集合について双方向に一致する。

forward:
- type decl があれば matching runtime binding がある

backward:
- runtime binding があれば matching type decl がある
-/
def frameDeclBindingExactAt (Γfr : TypeFrame) (σfr : ScopeFrame) : Prop :=
  (∀ x d,
      Γfr.decls x = some d →
      ∃ b, σfr.binds x = some b ∧ DeclMatchesBinding d b) ∧
  (∀ x b,
      σfr.binds x = some b →
      ∃ d, Γfr.decls x = some d ∧ DeclMatchesBinding d b)

/-- 各深さで frame-local exactness が成り立つ。 -/
def framewiseDeclBindingExact (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) Γfr σfr,
    Γ.scopes[k]? = some Γfr →
    σ.scopes[k]? = some σfr →
    frameDeclBindingExactAt Γfr σfr

/-- current type frame では名前 `x` がまだ宣言されていない。 -/
def currentTypeFrameFresh (Γ : TypeEnv) (x : Ident) : Prop :=
  ∀ Γfr, Γ.scopes[0]? = some Γfr → Γfr.decls x = none

/-- runtime に現れるすべての ref binding は live typed target を持つ。 -/
def allRuntimeRefBindingsLive (σ : State) : Prop :=
  ∀ {k : Nat} {x : Ident} {τ : CppType} {a : Nat},
    runtimeFrameBindsRef σ k x τ a →
    heapLiveTypedAt σ a τ

@[simp] theorem frameDeclBindingExactAt_forward
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    (h : frameDeclBindingExactAt Γfr σfr)
    {x : Ident} {d : DeclInfo} :
    Γfr.decls x = some d →
    ∃ b, σfr.binds x = some b ∧ DeclMatchesBinding d b :=
  h.1 x d

@[simp] theorem frameDeclBindingExactAt_backward
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    (h : frameDeclBindingExactAt Γfr σfr)
    {x : Ident} {b : Binding} :
    σfr.binds x = some b →
    ∃ d, Γfr.decls x = some d ∧ DeclMatchesBinding d b :=
  h.2 x b

/--
frame-local exactnessから、top type frame の freshness は
runtime top frame の freshness に落ちる。

注意:
- ここでは `lookup` の global iff は使わない。
- 必要なのは same-frame exactness だけである。
-/
theorem topFrameBindingFresh_of_framewiseExact_and_topTypeFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {Γfr : TypeFrame}
    (hexact : framewiseDeclBindingExact Γ σ)
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hfresh : Γfr.decls x = none) :
    topFrameBindingFresh σ x := by
  intro σfr hσ0
  have hExact0 : frameDeclBindingExactAt Γfr σfr :=
    hexact 0 Γfr σfr hΓ0 hσ0
  by_cases hnone : σfr.binds x = none
  · exact hnone
  · cases hbx : σfr.binds x with
    | none => contradiction
    | some b =>
        rcases frameDeclBindingExactAt_backward hExact0 hbx with ⟨d, hdecl, _⟩
        rw [hfresh] at hdecl
        simp at hdecl

/-- `currentTypeFrameFresh` をそのまま使う版。 -/
theorem topFrameBindingFresh_of_framewiseExact_and_currentTypeFrameFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {Γfr : TypeFrame}
    (hexact : framewiseDeclBindingExact Γ σ)
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hfresh : currentTypeFrameFresh Γ x) :
    topFrameBindingFresh σ x := by
  exact topFrameBindingFresh_of_framewiseExact_and_topTypeFresh
    (hexact := hexact) (hΓ0 := hΓ0) (hfresh := hfresh Γfr hΓ0)

/--
ref の全域 live 性があれば、`σ.next` を inner ref が指していることは起きない。

理由:
- inner ref が `σ.next` を指すなら、その target は live であるはず。
- しかし `nextFreshAgainstOwned` は `σ.heap σ.next = none` を含む。
- よって矛盾。
-/
theorem nextNotTargetOfInnerRefs_of_allRuntimeRefBindingsLive
    {σ : State}
    (hlive : allRuntimeRefBindingsLive σ)
    (hnext : nextFreshAgainstOwned σ) :
    nextNotTargetOfInnerRefs σ := by
  intro k x τ hk href
  rcases hlive href with ⟨c, hheap, _, _⟩
  rcases hnext with ⟨hnone, _⟩
  rw [hnone] at hheap
  simp at hheap

/--
中間解の strengthening package.

`ScopedTypedStateConcrete` 自体は宣言入力 `x` を持ち込まず、
ここで名前 exactness と runtime ref-live を別 package として追加する。
-/
structure ScopedTypedStateConcreteStrengthening
    (Γ : TypeEnv) (σ : State) : Prop where
  namesExact : framewiseDeclBindingExact Γ σ
  runtimeRefsLive : allRuntimeRefBindingsLive σ

/--
object declaration に必要な support package.

- base concrete invariant
- strengthening package
- current type frame freshness

`x` 依存なのは最後の `typeFresh` だけであり、
state invariant の本体は `ScopedTypedStateConcrete` に残す。
-/
structure DeclareObjectReadyStrong
    (Γ : TypeEnv) (σ : State) (x : Ident) : Prop where
  concrete : ScopedTypedStateConcrete Γ σ
  strengthening : ScopedTypedStateConcreteStrengthening Γ σ
  typeFresh : currentTypeFrameFresh Γ x

namespace DeclareObjectReadyStrong

/-- 明示的に top type frame witness が与えられている場合の name-side side condition. -/
theorem topFrameFresh
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    topFrameBindingFresh σ x := by
  exact topFrameBindingFresh_of_framewiseExact_and_currentTypeFrameFresh
    (hexact := h.strengthening.namesExact)
    (hΓ0 := hΓ0)
    (hfresh := h.typeFresh)

/-- address-side side condition は state-side strengthening だけで出る。 -/
theorem noInnerNextAlias
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x) :
    nextNotTargetOfInnerRefs σ := by
  exact nextNotTargetOfInnerRefs_of_allRuntimeRefBindingsLive
    (hlive := h.strengthening.runtimeRefsLive)
    (hnext := h.concrete.nextFresh)

/-- declaration theorem が必要とする二つの side condition をまとめる。 -/
theorem sideConditions
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    topFrameBindingFresh σ x ∧ nextNotTargetOfInnerRefs σ := by
  exact ⟨h.topFrameFresh hΓ0, h.noInnerNextAlias⟩

end DeclareObjectReadyStrong

end Cpp
