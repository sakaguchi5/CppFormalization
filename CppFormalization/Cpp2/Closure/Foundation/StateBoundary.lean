import CppFormalization.Cpp2.Static.Assumptions
import CppFormalization.Cpp2.Lemmas.RuntimeState

namespace Cpp

/-!
# Closure.Foundation.StateBoundary

Closure theorem へ向かうための「状態境界」と「開始準備条件」の層。

意図:
- 旧 `IdealAssumptions` を、そのまま closure の前提にしない。
- runtime invariant と statement-local safety を分ける。
- 既存 Core の theorem を壊さず、その上に乗る新しい境界語彙を用意する。
-/

/-- 型環境と runtime state の frame 数が一致する。第一近似として長さ一致だけを採用する。 -/
def scopesCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  Γ.scopes.length = σ.scopes.length

axiom framewiseDeclBindingCompatible : TypeEnv → State → Prop
axiom objectBindingsLiveTypedOwned : TypeEnv → State → Prop
axiom refBindingsLiveTyped : TypeEnv → State → Prop

/-- runtime frame 内で object binding が使っている address。 -/
def frameBindsObjectAddr (fr : ScopeFrame) (a : Nat) : Prop :=
  ∃ x τ, fr.binds x = some (.object τ a)

/--
各 runtime frame の `locals` は、その frame 内の object binding address とちょうど一致する。
ここでは type-env 側とは直接結び付けず、runtime frame 自体の整合条件として書く。
-/
def frameLocalsExact (_Γ : TypeEnv) (σ : State) : Prop :=
  ∀ (k : Nat) fr,  -- k が Nat であることを明示
    σ.scopes[k]? = some fr →
    ∀ a, a ∈ fr.locals ↔ frameBindsObjectAddr fr a

/-- 異なる frame の `locals` は交わらない。 -/
def ownedAddressesDisjoint (σ : State) : Prop :=
  ∀ (i j : Nat) fi fj a,
    i ≠ j →
    σ.scopes[i]? = some fi →
    σ.scopes[j]? = some fj →
    a ∈ fi.locals →
    a ∉ fj.locals

@[simp] theorem ownedAddressesDisjoint_writeHeap
    {σ : State} {a : Nat} {c : Cell} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (writeHeap σ a c) := by
  intro hdisj
  simpa [ownedAddressesDisjoint, writeHeap] using hdisj

@[simp] theorem ownedAddressesDisjoint_setNext
    {σ : State} {n : Nat} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint ({ σ with next := n }) := by
  intro hdisj
  simpa [ownedAddressesDisjoint] using hdisj

theorem ownedAddressesDisjoint_pushScope
    {σ : State} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (pushScope σ) := by
  intro hdisj
  unfold ownedAddressesDisjoint at *
  intro i j fi fj a hij hi hj hai
  cases i with
  | zero =>
      cases j with
      | zero =>
          exact (hij rfl).elim
      | succ j =>
          simp [pushScope, emptyScopeFrame] at hi
          subst fi
          simp at hai
  | succ i =>
      cases j with
      | zero =>
          simp [pushScope, emptyScopeFrame] at hj
          subst fj
          simp
      | succ j =>
          have hi_old : σ.scopes[i]? = some fi := by
            simpa [pushScope] using hi
          have hj_old : σ.scopes[j]? = some fj := by
            simpa [pushScope] using hj
          exact hdisj i j fi fj a
            (by
              intro hij'
              apply hij
              simp [hij'])
            hi_old hj_old hai

theorem ownedAddressesDisjoint_bindTopBinding
    {σ : State} {x : Ident} {b : Binding} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (bindTopBinding σ x b) := by
  intro hdisj
  unfold ownedAddressesDisjoint at *
  cases hsc : σ.scopes with
  | nil =>
      intro i j fi fj a hij hi hj hai
      cases i <;> cases j <;>
        simp [bindTopBinding, hsc] at hi hj hai
      -- i=0, j=0 のとき hij : 0 ≠ 0 となっているので contradiction で閉じれる
      contradiction
  | cons fr frs =>
      intro i j fi fj a hij hi hj hai
      cases i with
      | zero =>
          cases j with
          | zero =>
              exact (hij rfl).elim
          | succ j =>
              simp [bindTopBinding, hsc] at hi
              subst fi
              have hi_old : σ.scopes[0]? = some fr := by
                simp [hsc]
              have hj_old : σ.scopes[j.succ]? = some fj := by
                simpa [bindTopBinding, hsc] using hj
              have hai_old : a ∈ fr.locals := by
                simpa using hai
              exact hdisj 0 j.succ fr fj a
                (by simp)
                hi_old
                hj_old
                hai_old
      | succ i =>
          cases j with
          | zero =>
              simp [bindTopBinding, hsc] at hj
              subst fj
              have hi_old : σ.scopes[i.succ]? = some fi := by
                simpa [bindTopBinding, hsc] using hi
              have hj_old : σ.scopes[0]? = some fr := by
                simp [hsc]
              have hnot : a ∉ fr.locals :=
                hdisj i.succ 0 fi fr a
                  (Nat.succ_ne_zero _)
                  hi_old
                  hj_old
                  hai
              simpa using hnot
          | succ j =>
              have hi_old : σ.scopes[i.succ]? = some fi := by
                simpa [bindTopBinding, hsc] using hi
              have hj_old : σ.scopes[j.succ]? = some fj := by
                simpa [bindTopBinding, hsc] using hj
              exact hdisj i.succ j.succ fi fj a hij hi_old hj_old hai

@[simp] theorem ownedAddressesDisjoint_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    ownedAddressesDisjoint σ →
    ownedAddressesDisjoint (declareRefState σ τ x a) := by
  intro hdisj
  simpa [declareRefState] using
    (ownedAddressesDisjoint_bindTopBinding
      (σ := σ) (x := x) (b := .ref τ a) hdisj)



/-- heap に入っている initialized value は cell の型に整合する。 -/
def heapInitializedValuesTyped (σ : State) : Prop :=
  ∀ a c v,
    σ.heap a = some c →
    c.value = some v →
    ValueCompat v c.ty

/-- `next` は未使用で、どの frame の `locals` にも現れない。 -/
def nextIsFreshForOwnedHeap (σ : State) : Prop :=
  σ.heap σ.next = none ∧
  ∀ (k : Nat) fr,
    σ.scopes[k]? = some fr →
    σ.next ∉ fr.locals

theorem nextIsFreshForOwnedHeap_bindTopBinding
    {σ : State} {x : Ident} {b : Binding} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (bindTopBinding σ x b) := by
  intro h
  rcases h with ⟨hheap, hfresh⟩
  refine ⟨?_, ?_⟩
  case refine_1 =>
    -- ゴール: (bindTopBinding σ x b).heap (bindTopBinding σ x b).next = none
    -- bindTopBinding は heap も next も変更しないことを利用する
    rw [next_bindTopBinding, heap_bindTopBinding]
    exact hheap
  case refine_2 =>
    -- ゴール: ∀ k fr, (bindTopBinding σ x b).scopes[k]? = some fr → next ∉ fr.locals
    intro k fr h_spec
    rw [next_bindTopBinding]
    -- bindTopBinding は既存のフレームの locals を変更しない
    rw [scopes_bindTopBinding] at h_spec
    split at h_spec
    case h_1 =>
      -- スコープが空だった場合
      -- h_spec : [{ binds := ..., locals := [] }][k]? = some fr
      -- リストのサイズが1なので、k は 0 以外ありえないことを示す
      cases k with
      | zero =>
        -- k = 0 のとき
        simp at h_spec
        subst h_spec
        -- fr.locals は [] なので、何ものも属さない
        simp
      | succ k' =>
        -- k = k' + 1 のとき、要素1つのリストの index 1 以上は none になる
        simp at h_spec
    case h_2 =>
      -- σ.scopes = fr_top :: fr_rest の場合
      rename_i fr_top fr_rest h_scopes
      cases k with
      | zero =>
        -- k = 0 : 最上位フレームが更新されたケース
        -- h_spec から、更新されたフレームが fr であることを抽出する
        simp at h_spec
        subst h_spec
        -- bindTopBinding は locals を変更せず、fr_top.locals を保持する
        -- したがって、元の hfresh 0 fr_top ... を使って証明できる
        apply hfresh 0 fr_top
        simp [h_scopes]
      | succ k' =>
        -- k = k' + 1 : 2番目以降のフレームのケース
        -- これらのフレームは bindTopBinding によって変更されない
        simp at h_spec
        -- 元の hfresh (k' + 1) fr ... を適用
        apply hfresh (k' + 1) fr
        simp [h_scopes, h_spec]

@[simp] theorem nextIsFreshForOwnedHeap_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (declareRefState σ τ x a) := by
  intro h
  simpa [declareRefState] using
    (nextIsFreshForOwnedHeap_bindTopBinding (x := x) (b := .ref τ a) h)

@[simp] theorem nextIsFreshForOwnedHeap_pushScope
    {σ : State} :
    nextIsFreshForOwnedHeap σ →
    nextIsFreshForOwnedHeap (pushScope σ) := by
  intro h
  rcases h with ⟨hheap, hfresh⟩
  refine ⟨?_, ?_⟩
  · simpa [pushScope] using hheap
  · intro k fr hk
    cases k with
    | zero =>
        simp [pushScope, emptyScopeFrame] at hk
        subst fr
        simp
    | succ k =>
        have hk_old : σ.scopes[k]? = some fr := by
          simpa [pushScope] using hk
        exact hfresh k fr hk_old

/--
`TypedState` より強い runtime invariant.
核心は scope stack 対応と ownership discipline.
-/
structure ScopedTypedState (Γ : TypeEnv) (σ : State) : Prop where
  stackAligned : scopesCompatible Γ σ
  frameDeclBinding : framewiseDeclBindingCompatible Γ σ
  objectBindingsSound : objectBindingsLiveTypedOwned Γ σ
  refBindingsSound : refBindingsLiveTyped Γ σ
  localsExact : frameLocalsExact Γ σ
  ownedDisjoint : ownedAddressesDisjoint σ
  initializedValuesTyped : heapInitializedValuesTyped σ
  nextFresh : nextIsFreshForOwnedHeap σ

/--
`PlaceReady Γ σ p τ` は、`p` が現在の状態で安全に使える `τ`-place であること。
-/
def PlaceReady (Γ : TypeEnv) (σ : State) (p : PlaceExpr) (τ : CppType) : Prop :=
  HasPlaceType Γ p τ ∧
  NoInvalidRefPlace σ p

/--
`ExprReady Γ σ e τ` は、`e` が現在の状態で安全に評価できる `τ`-expr であること。
-/
def ExprReady (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) : Prop :=
  HasValueType Γ e τ ∧
  NoUninitValue σ e ∧
  NoInvalidRefValue σ e

/--
statement / block 開始時の安全準備条件。
`ScopedTypedState` が状態側、`StmtReady` / `BlockReady` が文局所側を受け持つ。
-/
def StmtReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  WellTypedFrom Γ st ∧
  NoUninitStmt σ st ∧
  NoInvalidRefStmt σ st

def BlockReady (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop :=
  (∃ Δ, HasTypeBlock Γ ss Δ) ∧
  NoUninitBlock σ ss ∧
  NoInvalidRefBlock σ ss

/--
closure theorem の本当の前提。
旧 `IdealAssumptions` をそのまま使わず、必要な層を明示的に分解する。
-/
structure BodyReady (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedState Γ σ
  safe : StmtReady Γ σ st

/- 未使用なのでコメントアウト
 theorem bodyReady_of_idealAssumptions
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : IdealAssumptions Γ σ st)
    (hstate : ScopedTypedState Γ σ) :
    BodyReady Γ σ st := by
  rcases h with ⟨hwf, htyped, htypedState, hnu, hnir, hbreak, hcont⟩
  exact
    { wf := hwf
      typed := htyped
      breakScoped := hbreak
      continueScoped := hcont
      state := hstate
      safe := ⟨htyped, hnu, hnir⟩ }
-/

end Cpp
