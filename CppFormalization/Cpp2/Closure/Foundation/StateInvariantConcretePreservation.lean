import CppFormalization.Cpp2.Static.Assumptions
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcretePreservationStage1

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
    exact ⟨fr, by simpa [pushScope] using hk, ha⟩
  · intro h
    rcases h with ⟨fr, hk, ha⟩
    exact ⟨fr, by simpa [pushScope] using hk, ha⟩

@[simp] theorem freshAddrAgainstOwned_pushScope_iff
    {σ : State} {a : Nat} :
    freshAddrAgainstOwned (pushScope σ) a ↔
      freshAddrAgainstOwned σ a := by
  unfold freshAddrAgainstOwned
  constructor
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · simpa [pushScope] using hheap
    · intro k fr hk
      exact hlocals k.succ fr (by simpa [pushScope] using hk)
  · intro h
    rcases h with ⟨hheap, hlocals⟩
    refine ⟨?_, ?_⟩
    · simpa [pushScope] using hheap
    · intro k fr hk
      cases k with
      | zero =>
          simp [pushScope, emptyScopeFrame] at hk
          subst fr
          simp
      | succ k =>
          exact hlocals k fr (by simpa [pushScope] using hk)

@[simp] theorem ownedAddressesNoDupPerFrame_pushScope
    {σ : State} :
    ownedAddressesNoDupPerFrame (pushScope σ) ↔ ownedAddressesNoDupPerFrame σ := by
  constructor
  · intro h k fr hk
    have hk' : (pushScope σ).scopes[k.succ]? = some fr := by
      simpa [pushScope] using hk
    exact h k.succ fr hk'
  · intro h k fr hk
    cases k with
    | zero =>
        simp [pushScope, emptyScopeFrame] at hk
        subst fr
        simp
    | succ k =>
        have hk_old : σ.scopes[k]? = some fr := by
          simpa [pushScope] using hk
        exact h k fr hk_old

@[simp] theorem ownedAddressesDisjointAcrossFrames_pushScope
    {σ : State} :
    ownedAddressesDisjointAcrossFrames (pushScope σ) ↔ ownedAddressesDisjointAcrossFrames σ := by
  constructor
  · intro h i j fi fj a hij hi hj hai
    intro haj
    have hown_i_new : runtimeFrameOwnsAddress (pushScope σ) i.succ a :=
      (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := i) (a := a)).2 ⟨fi, hi, hai⟩
    have hown_j_new : runtimeFrameOwnsAddress (pushScope σ) j.succ a :=
      (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := j) (a := a)).2 ⟨fj, hj, haj⟩
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
        exact runtimeFrameOwnsAddress_pushScope_zero_false
          (σ := σ) (a := a) ⟨fi, hi, hai⟩
    | succ i =>
        cases j with
        | zero =>
            exact runtimeFrameOwnsAddress_pushScope_zero_false
              (σ := σ) (a := a) ⟨fj, hj, haj⟩
        | succ j =>
            have hown_i_old : runtimeFrameOwnsAddress σ i a :=
              (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := i) (a := a)).1 ⟨fi, hi, hai⟩
            have hown_j_old : runtimeFrameOwnsAddress σ j a :=
              (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := j) (a := a)).1 ⟨fj, hj, haj⟩
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
      (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).2 hown
    rcases h _ _ hown' with ⟨x, τ, hbind⟩
    rcases hbind with ⟨fr, hk, hb⟩
    exact ⟨x, τ, ⟨fr, by simpa [pushScope] using hk, hb⟩⟩
  · intro h k a hown
    cases k with
    | zero =>
        exfalso
        exact runtimeFrameOwnsAddress_pushScope_zero_false
          (σ := σ) (a := a) hown
    | succ k =>
        have hown_old : runtimeFrameOwnsAddress σ k a :=
          (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).1 hown
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

/-- Top-frame binding update does not change `locals`. -/
@[simp] theorem locals_bindTopBinding_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} :
    ({ fr with binds := fun y => if y = x then some b else fr.binds y }).locals = fr.locals := by
  rfl

/-- `declareRefState` only changes the top frame; deeper scopes are untouched. -/
@[simp] theorem declareRefState_scopes_succ
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} {k : Nat} :
    (declareRefState σ τ x a).scopes[k.succ]? = σ.scopes[k.succ]? := by
  cases hsc : σ.scopes <;> simp [declareRefState, scopes_bindTopBinding, hsc]

@[simp] theorem declareRefState_lookup_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {fr : ScopeFrame} :
    (declareRefState σ τ x a).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  rw [declareRefState_scopes_succ]

@[simp] theorem declareRefState_scopes_zero_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs) :
    (declareRefState σ τ x a).scopes[0]? =
      some
        { fr0 with
          binds := fun y => if y = x then some (.ref τ a) else fr0.binds y } := by
  simp [declareRefState, scopes_bindTopBinding, hsc]

theorem declareRefState_lookup_zero_frame_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    fr =
      { fr0 with
        binds := fun y => if y = x then some (.ref τ a) else fr0.binds y } := by
  have htop := declareRefState_scopes_zero_of_cons
    (σ := σ) (τ := τ) (x := x) (a := a) (fr0 := fr0) (frs := frs) hsc
  exact Option.some.inj (hk.symm.trans htop)

theorem declareRefState_lookup_zero_locals_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    fr.locals = fr0.locals := by
  rcases declareRefState_lookup_zero_frame_of_cons
      (σ := σ) (τ := τ) (x := x) (a := a) (fr0 := fr0) (frs := frs) hsc hk with rfl
  simp

theorem declareRefState_lookup_preserves_locals_forward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {fr : ScopeFrame}
    (hk : σ.scopes[k]? = some fr) :
    ∃ fr',
      (declareRefState σ τ x a).scopes[k]? = some fr' ∧
      fr'.locals = fr.locals := by
  cases hsc : σ.scopes with
  | nil =>
      cases k <;> simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          refine ⟨
            { fr0 with binds := fun y => if y = x then some (.ref τ a) else fr0.binds y },
            ?_,
            ?_⟩
          · simp [declareRefState, scopes_bindTopBinding, hsc]
          · simp
      | succ k =>
          refine ⟨fr, ?_, rfl⟩
          exact (declareRefState_lookup_succ_iff
            (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (fr := fr)).2 hk

theorem declareRefState_lookup_preserves_locals_backward_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {k : Nat} {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[k]? = some fr) :
    ∃ fr',
      σ.scopes[k]? = some fr' ∧
      fr.locals = fr'.locals := by
  cases k with
  | zero =>
      refine ⟨fr0, by simp [hsc], ?_⟩
      exact declareRefState_lookup_zero_locals_of_cons
        (σ := σ) (τ := τ) (x := x) (a := a) (fr0 := fr0) (frs := frs) hsc hk
  | succ k =>
      refine ⟨fr, ?_, rfl⟩
      exact (declareRefState_lookup_succ_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (fr := fr)).1 hk

theorem runtimeFrameOwnsAddress_declareRefState_forward
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress σ k addr →
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr := by
  intro hown
  rcases hown with ⟨fr, hk, ha⟩
  rcases declareRefState_lookup_preserves_locals_forward
      (σ := σ) (τ := τ) (x := x) (a := a) hk with
    ⟨fr', hk', hlocals⟩
  refine ⟨fr', hk', ?_⟩
  simpa [hlocals] using ha

theorem runtimeFrameOwnsAddress_declareRefState_backward
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr →
    runtimeFrameOwnsAddress σ k addr := by
  intro hown
  rcases hown with ⟨fr, hk, ha⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp at ha
      | succ k =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
  | cons fr0 frs =>
      rcases declareRefState_lookup_preserves_locals_backward_of_cons
          (σ := σ) (τ := τ) (x := x) (a := a) hsc hk with
        ⟨fr', hk', hlocals⟩
      refine ⟨fr', hk', ?_⟩
      simpa [hlocals] using ha

@[simp] theorem runtimeFrameOwnsAddress_declareRefState_iff
    {σ : State} {τ : CppType} {x : Ident} {a addr : Nat} {k : Nat} :
    runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ↔
      runtimeFrameOwnsAddress σ k addr := by
  constructor
  · exact runtimeFrameOwnsAddress_declareRefState_backward
      (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (addr := addr)
  · exact runtimeFrameOwnsAddress_declareRefState_forward
      (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (addr := addr)

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
        (runtimeFrameOwnsAddress_declareRefState_iff
          (σ := σ) (τ := τ) (x := x) (a := r) (k := k) (addr := a)).2 hown_old
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
        (runtimeFrameOwnsAddress_declareRefState_iff
          (σ := σ) (τ := τ) (x := x) (a := r) (k := k) (addr := a)).1 hown_new
      rcases hown_old with ⟨fr', hk', hm'⟩
      exact hlocals k fr' hk' hm'

theorem declareRefState_frameLocalsNodup_backward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (h : ownedAddressesNoDupPerFrame σ)
    {k : Nat} {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[k]? = some fr) :
    fr.locals.Nodup := by
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp
      | succ k =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          have hlocals : fr.locals = fr0.locals :=
            declareRefState_lookup_zero_locals_of_cons
              (σ := σ) (τ := τ) (x := x) (a := a) (fr0 := fr0) (frs := frs) hsc hk
          have hnodup0 : fr0.locals.Nodup := h 0 fr0 (by simp [hsc])
          simpa [hlocals] using hnodup0
      | succ k =>
          have hk_old : σ.scopes[k.succ]? = some fr :=
            (declareRefState_lookup_succ_iff
              (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (fr := fr)).1 hk
          exact h k.succ fr hk_old

@[simp] theorem ownedAddressesNoDupPerFrame_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    ownedAddressesNoDupPerFrame (declareRefState σ τ x a) ↔
      ownedAddressesNoDupPerFrame σ := by
  constructor
  · intro h
    intro k fr hk
    rcases declareRefState_lookup_preserves_locals_forward
        (σ := σ) (τ := τ) (x := x) (a := a) hk with
      ⟨fr', hk', hlocals⟩
    have hnodup : fr'.locals.Nodup := h k fr' hk'
    simpa [hlocals] using hnodup
  · intro h
    intro k fr hk
    exact declareRefState_frameLocalsNodup_backward
      (σ := σ) (τ := τ) (x := x) (a := a) h hk

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
      (runtimeFrameOwnsAddress_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := i) (addr := addr)).2 hown_i_old
    have hown_j_new :
        runtimeFrameOwnsAddress (declareRefState σ τ x a) j addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := j) (addr := addr)).2 hown_j_old
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
      (runtimeFrameOwnsAddress_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := i) (addr := addr)).1 hown_i_new
    have hown_j_old :
        runtimeFrameOwnsAddress σ j addr :=
      (runtimeFrameOwnsAddress_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (a := a) (k := j) (addr := addr)).1 hown_j_new
    rcases hown_i_old with ⟨fi', hi', hai'⟩
    rcases hown_j_old with ⟨fj', hj', haj'⟩
    exact (h i j fi' fj' addr hij hi' hj' hai') haj'

end DeclareRefStatePreservation

section DeclareObjectStatePreservation

@[simp] theorem declareObjectState_scopes_succ
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {k : Nat} :
    (declareObjectState σ τ x ov).scopes[k.succ]? = σ.scopes[k.succ]? := by
  cases hsc : σ.scopes with
  | nil =>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc]
  | cons fr0 frs =>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc]

@[simp] theorem declareObjectState_scopes_zero_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs) :
    (declareObjectState σ τ x ov).scopes[0]? =
      some
        { fr0 with
          binds := fun y => if y = x then some (.object τ σ.next) else fr0.binds y
          locals := σ.next :: fr0.locals } := by
  simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc]

@[simp] theorem declareObjectState_lookup_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {fr : ScopeFrame} :
    (declareObjectState σ τ x ov).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  constructor <;> intro hk <;> simpa using hk

theorem declareObjectState_lookup_zero_frame_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr =
      { fr0 with
        binds := fun y => if y = x then some (.object τ σ.next) else fr0.binds y
        locals := σ.next :: fr0.locals } := by
  have htop := declareObjectState_scopes_zero_of_cons
    (σ := σ) (τ := τ) (x := x) (ov := ov) (fr0 := fr0) (frs := frs) hsc
  exact Option.some.inj (hk.symm.trans htop)

theorem declareObjectState_lookup_zero_locals_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr.locals = σ.next :: fr0.locals := by
  rcases declareObjectState_lookup_zero_frame_of_cons
      (σ := σ) (τ := τ) (x := x) (ov := ov) (fr0 := fr0) (frs := frs) hsc hk with rfl
  simp

@[simp] theorem locals_recordLocal_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} {a : Nat} :
    ({ fr with
        binds := fun y => if y = x then some b else fr.binds y
        locals := a :: fr.locals }).locals
      = a :: fr.locals := by
  rfl

theorem mem_declareObjectState_top_locals_iff
    {fr : ScopeFrame} {a b : Nat} {x : Ident} {τ : CppType} :
    a ∈ ({ fr with
      binds := fun y => if y = x then some (.object τ b) else fr.binds y,
      locals := b :: fr.locals }).locals
    ↔ a = b ∨ a ∈ fr.locals := by
  simp

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
  intro hsucc
  rcases hsucc with ⟨hheapSucc, hlocalsSucc⟩
  refine ⟨?_, ?_⟩
  · have hheap_keep :
        (declareObjectState σ τ x ov).heap (σ.next + 1) = σ.heap (σ.next + 1) := by
      simp
    calc
      (declareObjectState σ τ x ov).heap (declareObjectState σ τ x ov).next
          = (declareObjectState σ τ x ov).heap (σ.next + 1) := by simp [next_declareObjectState]
      _ = σ.heap (σ.next + 1) := hheap_keep
      _ = none := hheapSucc
  · intro k fr hk
    cases hsc : σ.scopes with
    | nil =>
        cases k with
        | zero =>
            simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc] at hk
            subst fr
            simp
        | succ k =>
            have hk_old : σ.scopes[k.succ]? = some fr :=
              (declareObjectState_lookup_succ_iff
                (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).1 hk
            simp [hsc] at hk_old
    | cons fr0 frs =>
        cases k with
        | zero =>
            rcases declareObjectState_lookup_zero_frame_of_cons
                (σ := σ) (τ := τ) (x := x) (ov := ov)
                (fr0 := fr0) (frs := frs) hsc hk with rfl
            have hnot_old : σ.next + 1 ∉ fr0.locals := by
              exact hlocalsSucc 0 fr0 (by simp [hsc])
            simp [next_declareObjectState, hnot_old]
        | succ k =>
            have hk_old : σ.scopes[k.succ]? = some fr :=
              (declareObjectState_lookup_succ_iff
                (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).1 hk
            simpa [next_declareObjectState] using hlocalsSucc k.succ fr hk_old

theorem ownedAddressesNoDupPerFrame_declareObjectState_of_nextFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ownedAddressesNoDupPerFrame σ →
    nextFreshAgainstOwned σ →
    ownedAddressesNoDupPerFrame (declareObjectState σ τ x ov) := by
  intro hnodup hfresh
  rcases hfresh with ⟨_, hfreshLocals⟩
  intro k fr hk
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [declareObjectState, recordLocal, bindTopBinding, hsc] at hk
          subst fr
          simp
      | succ k =>
          have hk_old : σ.scopes[k.succ]? = some fr :=
            (declareObjectState_lookup_succ_iff
              (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).1 hk
          simpa [hsc] using hnodup k.succ fr hk_old
  | cons fr0 frs =>
      cases k with
      | zero =>
          have hlocals : fr.locals = σ.next :: fr0.locals :=
            declareObjectState_lookup_zero_locals_of_cons
              (σ := σ) (τ := τ) (x := x) (ov := ov) (fr0 := fr0) (frs := frs) hsc hk
          have h0 : fr0.locals.Nodup := hnodup 0 fr0 (by simp [hsc])
          have hnot : σ.next ∉ fr0.locals := by
            exact hfreshLocals 0 fr0 (by simp [hsc])
          simpa [hlocals] using List.nodup_cons.2 ⟨hnot, h0⟩
      | succ k =>
          have hk_old : σ.scopes[k.succ]? = some fr :=
            (declareObjectState_lookup_succ_iff
              (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).1 hk
          exact hnodup k.succ fr hk_old

end DeclareObjectStatePreservation

end Cpp
