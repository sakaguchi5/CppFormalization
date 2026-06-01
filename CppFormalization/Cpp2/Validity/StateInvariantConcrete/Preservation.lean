import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete

namespace Cpp

/-!
# Static.Safety.StateInvariantConcrete.PreservationStage1

Stage 1 の第一便。

ここではまず、Foundation 側で最も壊れやすい runtime ownership / freshness /
initialized-value の primitive preservation を theorem として揃える。

重要な設計判断:
- `pushScope` は新しい空フレームを積むだけなので、既存 invariant の「添字ずれ」を先に整理する。
- `declareRefState` は heap / locals を変えないので、scope lookup と locals 不変を核にして ownership preservation を出す。
- `declareObjectState` は `next` が `σ.next + 1` に進むため、旧 `nextFreshAgainstOwned σ` だけでは新しい `next` の freshness は出ない。
  そこで任意 address 版の fresh predicate を切り出して、必要な side condition を明示する。
-/

section FreshnessAndOptionCompat

/-- 任意 address `a` が heap / owned-locals と衝突していない。 -/
def freshAddrAgainstOwned (σ : State) (a : Nat) : Prop :=
  σ.heap a = none ∧
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    a ∉ fr.locals

@[simp] theorem freshAddrAgainstOwned_at_next
    {σ : State} :
    freshAddrAgainstOwned σ σ.next ↔ nextFreshAgainstOwned σ := by
  rfl

/-- `Option Value` 版の型整合条件。 -/
def OptionValueCompat (ov : Option Value) (τ : CppType) : Prop :=
  match ov with
  | none => True
  | some v => ValueCompat v τ

@[simp] theorem OptionValueCompat_none {τ : CppType} :
    OptionValueCompat none τ := by
  simp [OptionValueCompat]

@[simp] theorem OptionValueCompat_some {v : Value} {τ : CppType} :
    OptionValueCompat (some v) τ ↔ ValueCompat v τ := by
  rfl

end FreshnessAndOptionCompat

section PushScopePreservation

@[simp] theorem frameDepthAgreement_pushScope
    {Γ : TypeEnv} {σ : State} :
    frameDepthAgreement (pushTypeScope Γ) (pushScope σ) ↔ frameDepthAgreement Γ σ := by
  unfold frameDepthAgreement pushTypeScope pushScope
  simp

@[simp] theorem heapInitializedValuesTyped_pushScope
    {σ : State} :
    heapInitializedValuesTyped (pushScope σ) ↔ heapInitializedValuesTyped σ := by
  unfold heapInitializedValuesTyped
  simp [pushScope]

@[simp] theorem runtimeFrameOwnsAddress_pushScope_zero_false
    {σ : State} {a : Nat} :
    ¬ runtimeFrameOwnsAddress (pushScope σ) 0 a := by
  intro h
  rcases h with ⟨fr, hk, ha⟩
  simp [pushScope, emptyScopeFrame] at hk
  subst fr
  simp at ha

@[simp] theorem runtimeFrameOwnsAddress_pushScope_succ_iff
    {σ : State} {k a : Nat} :
    runtimeFrameOwnsAddress (pushScope σ) k.succ a ↔
      runtimeFrameOwnsAddress σ k a := by
  constructor
  · intro h
    rcases h with ⟨fr, hk, ha⟩
    -- pushScope の定義を展開して、(x :: xs)[k.succ]? = xs[k]? を利用
    unfold pushScope at hk
    exact ⟨fr, hk, ha⟩
  · intro h
    rcases h with ⟨fr, hk, ha⟩
    unfold pushScope
    exact ⟨fr, hk, ha⟩

@[simp] theorem freshAddrAgainstOwned_pushScope_iff
    {σ : State} {a : Nat} :
    freshAddrAgainstOwned (pushScope σ) a ↔
      freshAddrAgainstOwned σ a := by
  unfold freshAddrAgainstOwned
  constructor
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · -- pushScope は heap を変更しない (rfl で解決)
      have : (pushScope σ).heap = σ.heap := rfl
      rw [this] at hheap
      exact hheap
    · intro k fr hk
      -- k 番目のスコープについて、(pushScope σ) の k.succ 番目として hlocals を適用
      unfold pushScope at hlocals
      exact hlocals k.succ fr hk
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · have : (pushScope σ).heap = σ.heap := rfl
      rw [this]
      exact hheap
    · intro k fr hk
      cases k with
      | zero =>
          -- 新規スコープは空なのでアドレス a は含まれない
          unfold pushScope at hk
          simp [emptyScopeFrame] at hk
          subst fr
          simp -- frameOwnsAddress emptyScopeFrame a は矛盾
      | succ k =>
          -- 1番目以降のスコープは元の σ の k 番目
          unfold pushScope at hk
          exact hlocals k fr hk

@[simp] theorem ownedAddressesNoDupPerFrame_pushScope
    {σ : State} :
    ownedAddressesNoDupPerFrame (pushScope σ) ↔ ownedAddressesNoDupPerFrame σ := by
  constructor
  · intro h k fr hk
    -- (pushScope σ) の k.succ 番目が fr であることを利用
    -- unfold pushScope により (emptyScopeFrame :: σ.scopes)[k.succ]? = σ.scopes[k]? となる
    unfold pushScope at h
    exact h k.succ fr hk
  · intro h k fr hk
    cases k with
    | zero =>
        -- 新しく積まれた 0 番目のスコープは空なので NoDup は自明
        unfold pushScope at hk
        simp [emptyScopeFrame] at hk
        subst fr
        simp
    | succ k =>
        -- 1 番目以降のスコープは元の σ の k 番目のスコープと同じ
        unfold pushScope at hk
        exact h k fr hk

@[simp] theorem ownedAddressesDisjointAcrossFrames_pushScope
    {σ : State} :
    ownedAddressesDisjointAcrossFrames (pushScope σ) ↔ ownedAddressesDisjointAcrossFrames σ := by
  constructor
  · intro h i j fi fj a hij hi hj hai
    intro haj
    have hown_i_new : runtimeFrameOwnsAddress (pushScope σ) i.succ a :=
      (runtimeFrameOwnsAddress_pushScope_succ_iff).2 ⟨fi, hi, hai⟩
    have hown_j_new : runtimeFrameOwnsAddress (pushScope σ) j.succ a :=
      (runtimeFrameOwnsAddress_pushScope_succ_iff).2 ⟨fj, hj, haj⟩
    rcases hown_i_new with ⟨fi', hi', hai'⟩
    rcases hown_j_new with ⟨fj', hj', haj'⟩
    exact (h i.succ j.succ fi' fj' a
      (by
        intro hEq
        apply hij
        exact Nat.succ.inj hEq)
      hi' hj' hai') haj'
  · intro h i j fi fj a hij hi hj hai
    intro haj
    cases i with
    | zero =>
        exfalso
        exact runtimeFrameOwnsAddress_pushScope_zero_false ⟨fi, hi, hai⟩
    | succ i =>
        cases j with
        | zero =>
            exact runtimeFrameOwnsAddress_pushScope_zero_false ⟨fj, hj, haj⟩
        | succ j =>
            have hown_i_old : runtimeFrameOwnsAddress σ i a :=
              (runtimeFrameOwnsAddress_pushScope_succ_iff ).1 ⟨fi, hi, hai⟩
            have hown_j_old : runtimeFrameOwnsAddress σ j a :=
              (runtimeFrameOwnsAddress_pushScope_succ_iff ).1 ⟨fj, hj, haj⟩
            rcases hown_i_old with ⟨fi', hi', hai'⟩
            rcases hown_j_old with ⟨fj', hj', haj'⟩
            exact (h i j fi' fj' a
              (by
                intro hEq
                apply hij
                simp [hEq])
              hi' hj' hai') haj'

@[simp] theorem allOwnedAddressesNamed_pushScope
    {σ : State} :
    allOwnedAddressesNamed (pushScope σ) ↔ allOwnedAddressesNamed σ := by
  constructor
  · intro h k a hown
    have hown' : runtimeFrameOwnsAddress (pushScope σ) k.succ a :=
      (runtimeFrameOwnsAddress_pushScope_succ_iff).2 hown
    rcases h _ _ hown' with ⟨x, τ, hbind⟩
    rcases hbind with ⟨fr, hk, hb⟩
    exact ⟨x, τ, ⟨fr, by simpa [pushScope] using hk, hb⟩⟩
  · intro h k a hown
    cases k with
    | zero =>
        exfalso
        exact runtimeFrameOwnsAddress_pushScope_zero_false hown
    | succ k =>
        have hown_old : runtimeFrameOwnsAddress σ k a :=
          (runtimeFrameOwnsAddress_pushScope_succ_iff).1 hown
        rcases h _ _ hown_old with ⟨x, τ, hbind_old⟩
        rcases hbind_old with ⟨fr', hk', hb'⟩
        exact ⟨x, τ, ⟨fr', by simpa [pushScope] using hk', hb'⟩⟩

end PushScopePreservation

section DeclareRefStatePreservation

@[simp] theorem heapInitializedValuesTyped_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    heapInitializedValuesTyped (declareRefState σ τ x a) ↔ heapInitializedValuesTyped σ := by
  unfold heapInitializedValuesTyped
  simp [declareRefState]

theorem runtimeFrameOwnsAddress_declareRefState_forward
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress σ k addr →
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr := by
  intro hown
  rcases hown with ⟨fr, hk, ha⟩
  rcases declareRefState_lookup_preserves_locals_forward hk with ⟨fr', hk', hlocals⟩
  refine ⟨fr', hk', ?_⟩
  simpa [hlocals] using ha

theorem runtimeFrameOwnsAddress_declareRefState_backward
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr →
    runtimeFrameOwnsAddress σ k addr := by
  intro hown
  rcases hown with ⟨fr, hk, ha⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp at ha
      | cons fr0 frs =>
          have hlocals : fr.locals = fr0.locals :=
            declareRefState_lookup_zero_locals_of_cons hsc hk
          refine ⟨fr0, by simp [hsc], ?_⟩
          simpa [hlocals] using ha
  | succ k =>
      have hk_old : σ.scopes[k.succ]? = some fr :=
        (declareRefState_lookup_succ_iff).1 hk
      exact ⟨fr, hk_old, ha⟩

@[simp] theorem runtimeFrameOwnsAddress_declareRefState_iff
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ↔
      runtimeFrameOwnsAddress σ k addr := by
  constructor
  · exact runtimeFrameOwnsAddress_declareRefState_backward
  · exact runtimeFrameOwnsAddress_declareRefState_forward

@[simp] theorem freshAddrAgainstOwned_declareRefState_iff
    {σ : State} {τ : CppType} {x : Ident} {r : Nat} {a : Nat} :
    freshAddrAgainstOwned (declareRefState σ τ x r) a ↔
      freshAddrAgainstOwned σ a := by
  unfold freshAddrAgainstOwned
  constructor
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · simpa [declareRefState] using hheap
    · intro k fr hk hmem
      have hown_old : runtimeFrameOwnsAddress σ k a := ⟨fr, hk, hmem⟩
      have hown_new :
          runtimeFrameOwnsAddress (declareRefState σ τ x r) k a :=
        (runtimeFrameOwnsAddress_declareRefState_iff).2 hown_old
      rcases hown_new with ⟨fr', hk', hm'⟩
      exact hlocals k fr' hk' hm'
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · simpa [declareRefState] using hheap
    · intro k fr hk hmem
      have hown_new :
          runtimeFrameOwnsAddress (declareRefState σ τ x r) k a := ⟨fr, hk, hmem⟩
      have hown_old :
          runtimeFrameOwnsAddress σ k a :=
        (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_new
      rcases hown_old with ⟨fr', hk', hm'⟩
      exact hlocals k fr' hk' hm'

theorem declareRefState_frameLocalsNodup_backward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (h : ownedAddressesNoDupPerFrame σ)
    {k : Nat} {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[k]? = some fr) :
    fr.locals.Nodup := by
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp
      | cons fr0 frs =>
          have hlocals : fr.locals = fr0.locals :=
            declareRefState_lookup_zero_locals_of_cons hsc hk
          have hnodup0 : fr0.locals.Nodup :=
            h 0 fr0 (by simp [hsc])
          simpa [hlocals] using hnodup0
  | succ k =>
      have hk_old : σ.scopes[k.succ]? = some fr :=
        (declareRefState_lookup_succ_iff).1 hk
      exact h k.succ fr hk_old

@[simp] theorem ownedAddressesNoDupPerFrame_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    ownedAddressesNoDupPerFrame (declareRefState σ τ x a) ↔
      ownedAddressesNoDupPerFrame σ := by
  constructor
  · intro h k fr hk
    rcases declareRefState_lookup_preserves_locals_forward hk with ⟨fr', hk', hlocals⟩
    exact hlocals ▸ (h k fr' hk')
  · intro h k fr hk
    -- 逆方向は既存の補題に丸ごと委ねる
    exact declareRefState_frameLocalsNodup_backward h hk

@[simp] theorem ownedAddressesDisjointAcrossFrames_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    ownedAddressesDisjointAcrossFrames (declareRefState σ τ x a) ↔
      ownedAddressesDisjointAcrossFrames σ := by
  constructor
  · intro h i j fi fj addr hij hi hj hai
    intro haj
    have hown_i_old : runtimeFrameOwnsAddress σ i addr := ⟨fi, hi, hai⟩
    have hown_j_old : runtimeFrameOwnsAddress σ j addr := ⟨fj, hj, haj⟩
    have hown_i_new :
        runtimeFrameOwnsAddress (declareRefState σ τ x a) i addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff).2 hown_i_old
    have hown_j_new :
        runtimeFrameOwnsAddress (declareRefState σ τ x a) j addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff).2 hown_j_old
    rcases hown_i_new with ⟨fi', hi', hai'⟩
    rcases hown_j_new with ⟨fj', hj', haj'⟩
    exact (h i j fi' fj' addr hij hi' hj' hai') haj'
  · intro h i j fi fj addr hij hi hj hai
    intro haj
    have hown_i_new :
        runtimeFrameOwnsAddress (declareRefState σ τ x a) i addr := ⟨fi, hi, hai⟩
    have hown_j_new :
        runtimeFrameOwnsAddress (declareRefState σ τ x a) j addr := ⟨fj, hj, haj⟩
    have hown_i_old :
        runtimeFrameOwnsAddress σ i addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_i_new
    have hown_j_old :
        runtimeFrameOwnsAddress σ j addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_j_new
    rcases hown_i_old with ⟨fi', hi', hai'⟩
    rcases hown_j_old with ⟨fj', hj', haj'⟩
    exact (h i j fi' fj' addr hij hi' hj' hai') haj'

end DeclareRefStatePreservation

section DeclareObjectStatePreservation

theorem heapInitializedValuesTyped_declareObjectState_of_optionCompat
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    heapInitializedValuesTyped σ →
    OptionValueCompat ov τ →
    heapInitializedValuesTyped (declareObjectState σ τ x ov) := by
  intro htyped hov
  intro a c v hc hv
  by_cases ha : a = σ.next
  · subst a
    cases hov_case : ov with
    | none =>
        simp [OptionValueCompat] at hov
        have hc' : c = { ty := τ, value := none, alive := true } := by
          apply Option.some.inj
          simpa [hov_case, eq_comm] using hc
        subst hc'
        simp at hv
    | some w =>
        simp [OptionValueCompat, hov_case] at hov
        have hc' : some c = some { ty := τ, value := some w, alive := true } := by
          simpa [hov_case, eq_comm] using hc
        have hcell : c = { ty := τ, value := some w, alive := true } := by
          exact Option.some.inj hc'
        subst hcell
        have hv'' : w = v := by
          have : some w = some v := by simpa [hov_case] using hv
          exact Option.some.inj this
        have hv' : v = w := hv''.symm
        subst hv'
        simpa using hov
  · have hc_old : σ.heap a = some c := by
        simpa [declareObjectState_heap_other (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) ha] using hc
    have hv_old : c.value = some v := hv
    exact htyped a c v hc_old hv_old

theorem nextFreshAgainstOwned_declareObjectState_of_freshSucc
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    freshAddrAgainstOwned σ (σ.next + 1) →
    nextFreshAgainstOwned (declareObjectState σ τ x ov) := by
  intro hfresh
  unfold freshAddrAgainstOwned nextFreshAgainstOwned at *
  constructor
  · rw [next_declareObjectState]
    rw [declareObjectState_heap_other]
    · exact hfresh.1
    · exact Nat.succ_ne_self σ.next
  · intro k fr hfr
    rw [next_declareObjectState]
    cases k with
    | zero =>
        cases hsc : σ.scopes with
        | nil =>
            have hlocals := declareObjectState_lookup_zero_locals_of_nil hsc hfr
            simp [hlocals, Nat.succ_ne_self]
        | cons fr0 frs =>
            have hlocals := declareObjectState_lookup_zero_locals_of_cons hsc hfr
            have hnotOld : σ.next + 1 ∉ fr0.locals :=
              hfresh.2 0 fr0 (by simp [hsc])
            simp [hlocals, Nat.succ_ne_self, hnotOld]
    | succ k =>
        exact hfresh.2 (Nat.succ k) fr (by
          exact (declareObjectState_lookup_succ_iff).1 hfr)

theorem ownedAddressesNoDupPerFrame_declareObjectState_of_nextFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ownedAddressesNoDupPerFrame σ →
    nextFreshAgainstOwned σ →
    ownedAddressesNoDupPerFrame (declareObjectState σ τ x ov) := by
  intro hNoDup hfresh
  unfold ownedAddressesNoDupPerFrame at hNoDup ⊢
  intro k fr hfr
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          have hlocals := declareObjectState_lookup_zero_locals_of_nil hsc hfr
          simp [hlocals]
      | cons fr0 frs =>
          have hlocals := declareObjectState_lookup_zero_locals_of_cons hsc hfr
          have hnotMem : σ.next ∉ fr0.locals :=
            hfresh.2 0 fr0 (by simp [hsc])
          have hNoDupTop : fr0.locals.Nodup :=
            hNoDup 0 fr0 (by simp [hsc])
          have hNew : (σ.next :: fr0.locals).Nodup := by
            constructor
            · intro a' ha hEq
              apply hnotMem
              simpa [hEq] using ha
            · exact hNoDupTop
          simpa [hlocals] using hNew
  | succ k =>
      exact hNoDup (Nat.succ k) fr (by
        simpa using hfr)

end DeclareObjectStatePreservation


/-! =========================================================
    Temporary lower API for downstream declare-object repair
    ========================================================= -/

section DeclareObjectStateLowerAPI

/-- Canonical API: the new object cell is stored at the pre-state cursor. -/
theorem declareObjectState_api_heap_new_cell
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    (declareObjectState σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  simp

/-- Canonical API: object declaration preserves every heap cell off the new address. -/
theorem declareObjectState_api_heap_off_new_cell
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} (ha : a ≠ σ.next) :
    (declareObjectState σ τ x ov).heap a = σ.heap a := by
  simpa using declareObjectState_heap_other σ τ x ov ha

/-- Case split for heap lookups after object declaration. -/
theorem declareObjectState_api_heap_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} {c : Cell}
    (hheap : (declareObjectState σ τ x ov).heap a = some c) :
    (a = σ.next ∧ c = { ty := τ, value := ov, alive := true }) ∨
      (a ≠ σ.next ∧ σ.heap a = some c) := by
  by_cases ha : a = σ.next
  · subst a
    have hnew : some { ty := τ, value := ov, alive := true } = some c := by
      simpa [declareObjectState_api_heap_new_cell] using hheap
    left
    exact ⟨rfl, (Option.some.inj hnew).symm⟩
  · right
    exact ⟨ha, by
      simpa [declareObjectState_api_heap_off_new_cell (σ := σ) (τ := τ)
        (x := x) (ov := ov) ha] using hheap⟩

/-- Canonical API: the object-declaration façade advances the cursor by successor. -/
theorem declareObjectState_api_next
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp

/-- Canonical API: deeper frames are unchanged by object declaration. -/
theorem declareObjectState_api_succ_scope_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {fr : ScopeFrame} :
    (declareObjectState σ τ x ov).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  exact declareObjectState_lookup_succ_iff

/-- Canonical API: top-frame locals after object declaration, split on old stack shape. -/
theorem declareObjectState_api_zero_locals_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr : ScopeFrame}
    (hfr : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    (σ.scopes = [] ∧ fr.locals = [σ.next]) ∨
      ∃ fr0 frs,
        σ.scopes = fr0 :: frs ∧ fr.locals = σ.next :: fr0.locals := by
  cases hsc : σ.scopes with
  | nil =>
      left
      exact ⟨rfl, declareObjectState_lookup_zero_locals_of_nil hsc hfr⟩
  | cons fr0 frs =>
      right
      exact ⟨fr0, frs, rfl, declareObjectState_lookup_zero_locals_of_cons hsc hfr⟩

/-- Canonical API: object declaration always owns the freshly allocated address in frame 0. -/
theorem declareObjectState_api_runtimeFrameOwnsAddress_zero_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 σ.next := by
  cases hsc : σ.scopes with
  | nil =>
      have hfr := declareObjectState_scopes_zero_of_nil
          (σ := σ) (τ := τ) (x := x) (ov := ov) hsc
      refine ⟨_, hfr, ?_⟩
      simp
  | cons fr0 frs =>
      have hfr := declareObjectState_scopes_zero_of_cons
          (σ := σ) (τ := τ) (x := x) (ov := ov)
          (fr0 := fr0) (frs := frs) hsc
      refine ⟨_, hfr, ?_⟩
      simp

/-- Canonical API: ownership in deeper frames is exactly preserved. -/
theorem declareObjectState_api_runtimeFrameOwnsAddress_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k a : Nat} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k.succ a ↔
      runtimeFrameOwnsAddress σ k.succ a := by
  constructor
  · intro hown
    rcases hown with ⟨fr, hfr, hmem⟩
    exact ⟨fr,
      (declareObjectState_api_succ_scope_iff).1 hfr,
      hmem⟩
  · intro hown
    rcases hown with ⟨fr, hfr, hmem⟩
    exact ⟨fr,
      (declareObjectState_api_succ_scope_iff).2 hfr,
      hmem⟩

/-- Canonical API: top-frame ownership after declaration is either the new address
or old top-frame ownership. -/
theorem declareObjectState_api_runtimeFrameOwnsAddress_zero_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat}
    (hown : runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 a) :
    a = σ.next ∨ runtimeFrameOwnsAddress σ 0 a := by
  rcases hown with ⟨fr, hfr, hmem⟩
  cases hsc : σ.scopes with
  | nil =>
      have hl := declareObjectState_lookup_zero_locals_of_nil hsc hfr
      simp [hl] at hmem
      exact Or.inl hmem
  | cons fr0 frs =>
      have hl := declareObjectState_lookup_zero_locals_of_cons hsc hfr
      simp [hl] at hmem
      rcases hmem with (rfl | hold)
      · exact Or.inl rfl
      · exact Or.inr ⟨fr0, by simp [hsc], hold⟩

/-- Canonical API: old top-frame ownership is preserved by object declaration. -/
theorem declareObjectState_api_runtimeFrameOwnsAddress_zero_preserved
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat}
    (hown : runtimeFrameOwnsAddress σ 0 a) :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 a := by
  rcases hown with ⟨fr, hfr, hmem⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      have hfr_eq : fr0 = fr := by
        simpa [hsc] using hfr
      subst fr
      have hfr_new := declareObjectState_scopes_zero_of_cons
          (σ := σ) (τ := τ) (x := x) (ov := ov)
          (fr0 := fr0) (frs := frs) hsc
      refine ⟨_, hfr_new, ?_⟩
      simp [hmem]

/-- Canonical API: initialized-value preservation for object declaration. -/
theorem declareObjectState_api_heapInitializedValuesTyped
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    heapInitializedValuesTyped σ →
    OptionValueCompat ov τ →
    heapInitializedValuesTyped (declareObjectState σ τ x ov) := by
  exact heapInitializedValuesTyped_declareObjectState_of_optionCompat

/-- Canonical API: successor-cursor freshness is the exact side condition needed
for preserving `nextFreshAgainstOwned`. -/
theorem declareObjectState_api_nextFreshAgainstOwned
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    freshAddrAgainstOwned σ (σ.next + 1) →
    nextFreshAgainstOwned (declareObjectState σ τ x ov) := by
  exact nextFreshAgainstOwned_declareObjectState_of_freshSucc

/-- Canonical API: object declaration preserves per-frame ownership nodup under
freshness of the newly allocated address. -/
theorem declareObjectState_api_ownedAddressesNoDupPerFrame
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ownedAddressesNoDupPerFrame σ →
    nextFreshAgainstOwned σ →
    ownedAddressesNoDupPerFrame (declareObjectState σ τ x ov) := by
  exact ownedAddressesNoDupPerFrame_declareObjectState_of_nextFresh

end DeclareObjectStateLowerAPI

end Cpp
