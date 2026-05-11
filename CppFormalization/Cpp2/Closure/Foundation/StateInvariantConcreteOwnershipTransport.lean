import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcretePreservation

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteOwnershipTransport

Stage 1 の後半。

ここでは `ScopedTypedStateConcreteOwnership` のうち、前便でまだ theorem-backed に
なっていなかった成分

- `allObjectBindingsOwned`
- `allOwnedAddressesNamed`
- `refBindingsNeverOwned`
- `refTargetsAvoidInnerOwned`

の transport を、`declareRefState` / `declareObjectState` ごとに切り分けて与える。

重要な設計判断:
- declaration 系 state update は top-frame の `binds` を上書きする。
  したがって old top binding を壊さないために、name freshness を明示仮定として切る。
- `declareRefState` では ownership 自体は変わらないので、`ownedNamed` から
  `refsNotOwned` を直接再構成できる。
- `declareObjectState` では新しい owner `σ.next` が top frame に追加されるため、
  深い frame の ref が `σ.next` を指していると `refTargetsAvoidInnerOwned` が壊れる。
  これも side condition として露出させる。
-/

/-- top frame では名前 `x` がまだ束縛されていない。 -/
def topFrameBindingFresh (σ : State) (x : Ident) : Prop :=
  ∀ fr, σ.scopes[0]? = some fr → fr.binds x = none

/-- 新しい allocation cursor `σ.next` を、top 以外の ref が指していない。 -/
def nextNotTargetOfInnerRefs (σ : State) : Prop :=
  ∀ {k : Nat} {x : Ident} {τ : CppType},
    0 < k →
    ¬ runtimeFrameBindsRef σ k x τ σ.next


section OwnershipTransportLocalAPI

@[simp] theorem topFrameBindingFresh_zero_of_cons
    {σ : State} {x : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs) :
    fr0.binds x = none := by
  exact hfresh fr0 (by simp [hsc])

theorem runtimeFrameBindsObject_top_name_ne_declared_of_topFresh
    {σ : State} {x y : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    {υ : CppType} {addr : Nat}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs)
    (hb : fr0.binds y = some (.object υ addr)) :
    y ≠ x := by
  intro hEq
  subst y
  rw [topFrameBindingFresh_zero_of_cons hfresh hsc] at hb
  simp at hb

theorem lookup_some_frame_eq
    {σ : State} {k : Nat} {fr fr' : ScopeFrame}
    (hk : σ.scopes[k]? = some fr)
    (hk' : σ.scopes[k]? = some fr') :
    fr = fr' := by
  rw [hk] at hk'
  injection hk'


/-- Backward-compatible name. -/
@[simp] theorem topFrameBindingFresh_of_cons
    {σ : State} {x : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs) :
    fr0.binds x = none := by
  exact topFrameBindingFresh_zero_of_cons hfresh hsc

/-- Backward-compatible name. -/
theorem objectBinding_name_ne_declared_of_topFresh
    {σ : State} {x y : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    {υ : CppType} {addr : Nat}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs)
    (hb : fr0.binds y = some (.object υ addr)) :
    y ≠ x := by
  exact runtimeFrameBindsObject_top_name_ne_declared_of_topFresh hfresh hsc hb

/-- Backward-compatible name. -/
theorem scope_lookup_some_frame_eq
    {σ : State} {k : Nat} {fr fr' : ScopeFrame}
    (hk : σ.scopes[k]? = some fr)
    (hk' : σ.scopes[k]? = some fr') :
    fr = fr' := by
  exact lookup_some_frame_eq (σ := σ) (k := k) hk hk'

end OwnershipTransportLocalAPI


section DeclareRefStateOwnershipTransport

 theorem runtimeFrameBindsObject_declareRefState_backward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareRefState σ τ x a) k y υ addr →
    runtimeFrameBindsObject σ k y υ addr := by
  intro hobj
  rcases hobj with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp at hb
      | succ k =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases declareRefState_lookup_zero_frame_of_cons
            (σ := σ) (τ := τ) (x := x) (a := a)
            (fr0 := fr0) (frs := frs) hsc hk with rfl
          by_cases hy : y = x
          · subst hy
            simp at hb
          · refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareRefState_lookup_succ_iff).1 hk

 theorem runtimeFrameBindsObject_declareRefState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject σ k y υ addr →
    runtimeFrameBindsObject (declareRefState σ τ x a) k y υ addr := by
  intro hobj
  rcases hobj with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero => simp [hsc] at hk
      | succ k => simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          have hyx : y ≠ x :=
            runtimeFrameBindsObject_top_name_ne_declared_of_topFresh hfresh hsc hb
          refine ⟨
            { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z },
            ?_, ?_⟩
          · simp [declareRefState, scopes_bindTopBinding, hsc]
          · simpa [hyx] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareRefState_lookup_succ_iff).2 hk

 theorem runtimeFrameBindsRef_declareRefState_cases
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr →
      (k = 0 ∧ y = x ∧ υ = τ ∧ addr = a) ∨
      runtimeFrameBindsRef σ k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [declareRefState, scopes_bindTopBinding, hsc] at hk
          subst fr
          simp at hb
          -- hb は (if y = x then some (.ref τ a) else none) = some (.ref υ addr)
          left       -- ゴールの「(k = 0 ∧ y = x ∧ υ = τ ∧ addr = a) ∨ ...」の左側を選択
          -- あとは hb の中身と k=0 (zero のケースなので自明) を使って終了
          simp [hb]
      | succ k => simp [declareRefState, scopes_bindTopBinding, hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases declareRefState_lookup_zero_frame_of_cons
            (σ := σ) (τ := τ) (x := x) (a := a)
            (fr0 := fr0) (frs := frs) hsc hk with rfl
          by_cases hy : y = x
          · subst hy
            have hb' : some (Binding.ref τ a) = some (.ref υ addr) := by
              simpa using hb
            have hEq : (Binding.ref τ a) = (.ref υ addr) := Option.some.inj hb'
            cases hEq
            exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
          · exact Or.inr ⟨fr0, by simp [hsc], by simpa [hy] using hb⟩
      | succ k =>
          exact Or.inr ⟨fr, (declareRefState_lookup_succ_iff).1 hk, hb⟩

 theorem allObjectBindingsOwned_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (howned : allObjectBindingsOwned σ) :
    allObjectBindingsOwned (declareRefState σ τ x a) := by
  intro k y υ addr hobj
  have hobj_old : runtimeFrameBindsObject σ k y υ addr :=
    runtimeFrameBindsObject_declareRefState_backward
      (σ := σ) (τ := τ) (x := x) (a := a) hobj
  have hown_old : runtimeFrameOwnsAddress σ k addr :=
    howned k y υ addr hobj_old
  exact (runtimeFrameOwnsAddress_declareRefState_iff).2 hown_old

 theorem allOwnedAddressesNamed_declareRefState_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    allOwnedAddressesNamed (declareRefState σ τ x a) := by
  intro k addr hown_new
  have hown_old : runtimeFrameOwnsAddress σ k addr :=
    (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_new
  rcases hnamed k addr hown_old with ⟨y, υ, hobj_old⟩
  exact ⟨y, υ,
    runtimeFrameBindsObject_declareRefState_forward_of_topFresh
      (σ := σ) (τ := τ) (x := x) (a := a) hfresh hobj_old⟩

 theorem refBindingsNeverOwned_declareRefState_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    refBindingsNeverOwned (declareRefState σ τ x a) := by
  intro k fr y υ addr hk href hmem
  have hown_new : runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr :=
    ⟨fr, hk, hmem⟩
  have hown_old : runtimeFrameOwnsAddress σ k addr :=
    (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_new
  rcases hnamed k addr hown_old with ⟨z, β, hobj_old⟩
  -- 定理を呼び出して、新しい状態での Exists を得る
  have hobj_new := runtimeFrameBindsObject_declareRefState_forward_of_topFresh
                     (σ := σ) (τ := τ) (x := x) (a := a) hfresh hobj_old
  -- Exists を分解して、具体的なフレーム fr' を取り出す
  rcases hobj_new with ⟨fr', hk', hb'⟩
  -- hk と hk' はどちらも (declareRefState ...).scopes[k]? なので、fr = fr' である
  have heq : fr = fr' :=
    lookup_some_frame_eq (σ := declareRefState σ τ x a) (k := k) hk hk'
  subst fr' -- fr' を fr に置き換える
  exact ⟨z, β, hb'⟩

 theorem refTargetsAvoidInnerOwned_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {r : Nat}
    (havoid : ∀ {k : Nat} {y : Ident} {υ : CppType} {a : Nat} {j : Nat},
      runtimeFrameBindsRef σ k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ j a) :
    ∀ {k : Nat} {y : Ident} {υ : CppType} {a : Nat} {j : Nat},
      runtimeFrameBindsRef (declareRefState σ τ x r) k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareRefState σ τ x r) j a := by
  intro k y υ a j href hjk hown_new
  rcases runtimeFrameBindsRef_declareRefState_cases
    (σ := σ) (τ := τ) (x := x) (a := r) href with hself | hold
  · rcases hself with ⟨hk0, _, _, _⟩
    subst k
    exact Nat.not_lt_zero _ hjk
  · have hown_old : runtimeFrameOwnsAddress σ j a :=
      (runtimeFrameOwnsAddress_declareRefState_iff).1 hown_new
    exact havoid hold hjk hown_old

end DeclareRefStateOwnershipTransport

section DeclareObjectStateOwnershipTransport

/-- Canonical API: deeper object bindings are exactly preserved. -/
theorem declareObjectState_api_runtimeFrameBindsObject_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) k.succ y υ addr ↔
      runtimeFrameBindsObject σ k.succ y υ addr := by
  constructor
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr,(declareObjectState_api_succ_scope_iff).1 hfr,hb⟩
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr,(declareObjectState_api_succ_scope_iff).2 hfr,hb⟩

/-- Canonical API: old top object bindings whose name is not `x` are preserved. -/
theorem declareObjectState_api_runtimeFrameBindsObject_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (hobj : runtimeFrameBindsObject σ 0 y υ addr) :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 y υ addr := by
  rcases hobj with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      refine ⟨
        { fr0 with
          binds := fun z => if z = x then some (.object τ σ.next) else fr0.binds z,
          locals := σ.next :: fr0.locals },
        ?_, ?_⟩
      ·
        exact declareObjectState_scopes_zero_of_cons
          (σ := σ) (τ := τ) (x := x) (ov := ov)
          (fr0 := fr0) (frs := frs) hsc
      · simpa [hy] using hb

 theorem runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject σ k y υ addr →
    runtimeFrameBindsObject (declareObjectState σ τ x ov) k y υ addr := by
  intro hobj
  cases k with
  | zero =>
      rcases hobj with ⟨fr, hfr, hb⟩
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hfr
      | cons fr0 frs =>
          simp [hsc] at hfr
          subst fr
          have hy : y ≠ x :=
            runtimeFrameBindsObject_top_name_ne_declared_of_topFresh hfresh hsc hb
          exact
            declareObjectState_api_runtimeFrameBindsObject_zero_preserved_of_ne hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact
        (declareObjectState_api_runtimeFrameBindsObject_succ_iff).2 hobj

 theorem runtimeFrameBindsObject_declareObjectState_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) k y υ addr →
      (k = 0 ∧ y = x ∧ υ = τ ∧ addr = σ.next) ∨
      runtimeFrameBindsObject σ k y υ addr := by
  intro hobj
  rcases hobj with ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          have hfr :
              fr =
                { binds := fun z =>
                    if z = x then some (.object τ σ.next) else emptyScopeFrame.binds z
                  locals := [σ.next] } := by
            simpa [declareObjectState_scopes_zero_of_nil hsc] using hk.symm
          subst fr
          by_cases hy : y = x
          · subst y
            have hb' : some (Binding.object τ σ.next) = some (.object υ addr) := by
              simpa using hb
            have hEq : (Binding.object τ σ.next) = (.object υ addr) :=
              Option.some.inj hb'
            cases hEq
            exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
          · simp [hy, emptyScopeFrame] at hb
      | cons fr0 frs =>
          rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hy : y = x
          · subst y
            have hb' : some (Binding.object τ σ.next) = some (.object υ addr) := by
              simpa using hb
            have hEq : (Binding.object τ σ.next) = (.object υ addr) :=
              Option.some.inj hb'
            cases hEq
            exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
          · exact Or.inr ⟨fr0, by simp [hsc], by simpa [hy] using hb⟩
  | succ k =>
      exact Or.inr ⟨fr,
        (declareObjectState_lookup_succ_iff).1 hk,hb⟩

 theorem runtimeFrameBindsRef_declareObjectState_backward
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ addr →
    runtimeFrameBindsRef σ k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          have hzero := declareObjectState_scopes_zero_of_nil
            (σ := σ) (τ := τ) (x := x) (ov := ov) hsc
          rw [hk] at hzero
          injection hzero with hfr
          subst fr
          by_cases hy : y = x
          · subst y
            simp at hb
          · simp [hy] at hb
      | cons fr0 frs =>
          rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hy : y = x
          · subst y
            simp at hb
          · exact ⟨fr0, by simp [hsc], by simpa [hy] using hb⟩
  | succ k =>
      exact ⟨fr,(declareObjectState_api_succ_scope_iff).1 hk,hb⟩

 theorem runtimeFrameOwnsAddress_declareObjectState_forward
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress σ k addr →
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k addr := by
  intro hown
  cases k with
  | zero =>
      exact declareObjectState_api_runtimeFrameOwnsAddress_zero_preserved hown
  | succ k =>
      exact (declareObjectState_api_runtimeFrameOwnsAddress_succ_iff).2 hown

 theorem runtimeFrameOwnsAddress_declareObjectState_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k addr →
      (k = 0 ∧ addr = σ.next) ∨ runtimeFrameOwnsAddress σ k addr := by
  intro hown
  cases k with
  | zero =>
      rcases declareObjectState_api_runtimeFrameOwnsAddress_zero_cases
          (σ := σ) (τ := τ) (x := x) (ov := ov)
          (a := addr) hown with hnew | hold
      · exact Or.inl ⟨rfl, hnew⟩
      · exact Or.inr hold
  | succ k =>
      exact Or.inr ((declareObjectState_api_runtimeFrameOwnsAddress_succ_iff).1 hown)

 theorem runtimeFrameBindsObject_declareObjectState_zero_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next := by
  refine ⟨fr, hk, ?_⟩
  cases hsc : σ.scopes with
  | nil =>
      have hzero := declareObjectState_scopes_zero_of_nil
        (σ := σ) (τ := τ) (x := x) (ov := ov) hsc
      rw [hk] at hzero
      injection hzero with hfr
      subst fr
      simp
  | cons fr0 frs =>
      rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
      simp

/-- Backward-compatible name. -/
 theorem runtimeFrameBindsObject_declareObjectState_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next := by
  exact runtimeFrameBindsObject_declareObjectState_zero_new
    (σ := σ) (τ := τ) (x := x) (ov := ov) hk

 theorem allObjectBindingsOwned_declareObjectState
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (howned : allObjectBindingsOwned σ) :
    allObjectBindingsOwned (declareObjectState σ τ x ov) := by
  intro k y υ addr hobj_new
  rcases runtimeFrameBindsObject_declareObjectState_cases
      (σ := σ) (τ := τ) (x := x) (ov := ov) hobj_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl, rfl, rfl⟩
    exact declareObjectState_api_runtimeFrameOwnsAddress_zero_new
  · have hown_old : runtimeFrameOwnsAddress σ k addr :=
      howned k y υ addr hold
    exact runtimeFrameOwnsAddress_declareObjectState_forward hown_old

 theorem allOwnedAddressesNamed_declareObjectState_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    allOwnedAddressesNamed (declareObjectState σ τ x ov) := by
  intro k addr hown_new
  rcases runtimeFrameOwnsAddress_declareObjectState_cases
      (σ := σ) (τ := τ) (x := x) (ov := ov) hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    rcases hown_new with ⟨fr, hk, _hmem⟩
    exact ⟨x, τ,
      runtimeFrameBindsObject_declareObjectState_zero_new
        (σ := σ) (τ := τ) (x := x) (ov := ov) hk⟩
  · rcases hnamed k addr hold with ⟨y, υ, hobj_old⟩
    exact ⟨y, υ,
      runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (ov := ov) hfresh hobj_old⟩

 theorem refBindingsNeverOwned_declareObjectState_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    refBindingsNeverOwned (declareObjectState σ τ x ov) := by
  intro k fr y υ addr hk href hmem
  have hown_new : runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k addr :=
    ⟨fr, hk, hmem⟩
  rcases runtimeFrameOwnsAddress_declareObjectState_cases
      (σ := σ) (τ := τ) (x := x) (ov := ov) hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    rcases runtimeFrameBindsObject_declareObjectState_zero_new
        (σ := σ) (τ := τ) (x := x) (ov := ov) hk with
      ⟨fr', hk', hb'⟩
    have heq : fr = fr' :=
      lookup_some_frame_eq
        (σ := declareObjectState σ τ x ov) (k := 0) hk hk'
    subst fr'
    exact ⟨x, τ, hb'⟩
  · rcases hnamed k addr hold with ⟨z, β, hobj_old⟩
    rcases runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
        (σ := σ) (τ := τ) (x := x) (ov := ov) hfresh hobj_old with
      ⟨fr', hk', hb'⟩
    have heq : fr = fr' :=
      lookup_some_frame_eq
        (σ := declareObjectState σ τ x ov) (k := k) hk hk'
    subst fr'
    exact ⟨z, β, hb'⟩

 theorem refTargetsAvoidInnerOwned_declareObjectState_of_noInnerNextAlias
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (havoid : ∀ {k : Nat} {y : Ident} {υ : CppType} {a : Nat} {j : Nat},
      runtimeFrameBindsRef σ k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ j a)
    (hnoNext : nextNotTargetOfInnerRefs σ) :
    ∀ {k : Nat} {y : Ident} {υ : CppType} {a : Nat} {j : Nat},
      runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareObjectState σ τ x ov) j a := by
  intro k y υ a j href_new hjk hown_new
  have href_old : runtimeFrameBindsRef σ k y υ a :=
    runtimeFrameBindsRef_declareObjectState_backward
      (σ := σ) (τ := τ) (x := x) (ov := ov) href_new
  rcases runtimeFrameOwnsAddress_declareObjectState_cases
    (σ := σ) (τ := τ) (x := x) (ov := ov) hown_new with hnew | hold
  · rcases hnew with ⟨hj0, hEq⟩
    subst j
    subst a
    exact hnoNext hjk href_old
  · exact havoid href_old hjk hold

end DeclareObjectStateOwnershipTransport

end Cpp
