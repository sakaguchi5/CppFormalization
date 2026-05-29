import CppFormalization.Cpp2.Validity.StateInvariantConcrete.Preservation
import CppFormalization.Cpp2.RuntimeModel.Facts.RuntimeDeclUpdate
namespace Cpp

/-!
# Static.Safety.StateInvariantConcrete.OwnershipTransport

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

theorem runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
    {σ : State} {x y : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    {υ : CppType} {addr : Nat}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs)
    (hb : fr0.binds y = some (.ref υ addr)) :
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

/-- Canonical API: deeper object bindings are exactly preserved by ref declarations. -/
theorem declareRefState_api_runtimeFrameBindsObject_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareRefState σ τ x a) k.succ y υ addr ↔
      runtimeFrameBindsObject σ k.succ y υ addr := by
  constructor
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareRefState_lookup_succ_iff).1 hfr, hb⟩
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareRefState_lookup_succ_iff).2 hfr, hb⟩

/-- Canonical API: old top object bindings whose name is not `x` are preserved. -/
theorem declareRefState_api_runtimeFrameBindsObject_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {a : Nat}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (hobj : runtimeFrameBindsObject σ 0 y υ addr) :
    runtimeFrameBindsObject (declareRefState σ τ x a) 0 y υ addr := by
  rcases hobj with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      exact ⟨_, declareRefState_scopes_zero_of_cons hsc, by simpa [hy] using hb⟩

/-- Canonical API: deeper ref bindings are exactly preserved by ref declarations. -/
theorem declareRefState_api_runtimeFrameBindsRef_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareRefState σ τ x a) k.succ y υ addr ↔
      runtimeFrameBindsRef σ k.succ y υ addr := by
  constructor
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareRefState_lookup_succ_iff).1 hfr, hb⟩
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareRefState_lookup_succ_iff).2 hfr, hb⟩

/-- Canonical API: old top ref bindings whose name is not `x` are preserved. -/
theorem declareRefState_api_runtimeFrameBindsRef_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {a : Nat}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (href : runtimeFrameBindsRef σ 0 y υ addr) :
    runtimeFrameBindsRef (declareRefState σ τ x a) 0 y υ addr := by
  rcases href with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      exact ⟨_, declareRefState_scopes_zero_of_cons hsc, by simpa [hy] using hb⟩

/-- Canonical API: a ref declaration binds the declared name in the top frame. -/
theorem declareRefState_api_runtimeFrameBindsRef_zero_new
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ a := by
  refine ⟨fr, hk, ?_⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [declareRefState, scopes_bindTopBinding, hsc] at hk
      subst fr
      simp
  | cons fr0 frs =>
      rcases declareRefState_lookup_zero_frame_of_cons hsc hk with rfl
      simp

theorem declareRefState_api_runtimeFrameBindsRef_top_new
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} :
    runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ a := by
  have hkσ0 : ∃ fr, (declareRefState σ τ x a).scopes[0]? = some fr := by
    cases hσ : σ.scopes <;>
      simp [declareRefState, bindTopBinding, hσ]
  rcases hkσ0 with ⟨fr, hk⟩
  exact declareRefState_api_runtimeFrameBindsRef_zero_new hk

theorem runtimeFrameBindsRef_declareRefState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr := by
  intro href
  cases k with
  | zero =>
      rcases href with ⟨fr, hfr, hb⟩
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hfr
      | cons fr0 frs =>
          simp [hsc] at hfr
          subst fr
          have hy : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh hfresh hsc hb
          exact
            declareRefState_api_runtimeFrameBindsRef_zero_preserved_of_ne
              hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact (declareRefState_api_runtimeFrameBindsRef_succ_iff).2 href


theorem runtimeFrameBindsObject_declareRefState_backward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareRefState σ τ x a) k y υ addr →
    runtimeFrameBindsObject σ k y υ addr := by
  intro ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          -- σ.scopes = [] の場合、declareRefState は空フレームを作るが
          -- その中身は Ref のみなので、hb (Object) と矛盾する
          simp [declareRefState, hsc] at hk; subst fr
          simp at hb
      | cons fr0 frs =>
          -- k=0 かつコンスケース：自作補題で fr の中身を特定
          rcases declareRefState_lookup_zero_frame_of_cons hsc hk with rfl
          -- y = x のときは Object ではなく Ref が入っているので矛盾
          by_cases hyx : y = x
          · subst hyx
            simp at hb
          · -- y ≠ x のときは、元のフレーム fr0 に Object があったはず
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hyx] using hb
  | succ k =>
      -- 深い階層は declareRefState_lookup_succ_iff の逆方向 (.1) で一発
      exact ⟨fr, declareRefState_lookup_succ_iff.1 hk, hb⟩

theorem runtimeFrameBindsObject_declareRefState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject σ k y υ addr →
    runtimeFrameBindsObject (declareRefState σ τ x a) k y υ addr := by
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
            declareRefState_api_runtimeFrameBindsObject_zero_preserved_of_ne
              hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact (declareRefState_api_runtimeFrameBindsObject_succ_iff).2 hobj

theorem runtimeFrameBindsRef_declareRefState_cases
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr →
      (k = 0 ∧ y = x ∧ υ = τ ∧ addr = a) ∨
      runtimeFrameBindsRef σ k y υ addr := by
  intro ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          -- σ.scopes = [] でも k=0 ならフレームが作られる
          simp [declareRefState, hsc] at hk; subst fr
          simp at hb
          -- hb : (if y = x then some (.ref τ a) else none) = some (.ref υ addr)
          -- これから y = x である必要があり、かつ中身が一致することを simp で解く
          left
          simp_all
      | cons fr0 frs =>
          rcases declareRefState_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hyx : y = x
          · left
            simp_all -- k=0, y=x, 中身の一致を一気に解決
          · right
            exact ⟨fr0, by simp [hsc], by simpa [hyx] using hb⟩
  | succ k =>
      -- 深い階層は常に元の状態にある (Or.inr)
      right
      exact ⟨fr, declareRefState_lookup_succ_iff.1 hk, hb⟩

 theorem allObjectBindingsOwned_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (howned : allObjectBindingsOwned σ) :
    allObjectBindingsOwned (declareRefState σ τ x a) := by
  intro k y υ addr hobj
  have hobj_old : runtimeFrameBindsObject σ k y υ addr :=
    runtimeFrameBindsObject_declareRefState_backward hobj
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
  exact ⟨y, υ, runtimeFrameBindsObject_declareRefState_forward_of_topFresh hfresh hobj_old⟩

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
  let hobj_new := runtimeFrameBindsObject_declareRefState_forward_of_topFresh
      (σ := σ) (τ := τ) (x := x) (a := a) hfresh hobj_old
  rcases hobj_new with ⟨fr', hk', hb'⟩
  have heq : fr = fr' := lookup_some_frame_eq hk hk'
  subst fr'
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
  rcases runtimeFrameBindsRef_declareRefState_cases href with hself | hold
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
      simp [hsc] at hfr; subst fr
      refine ⟨_, declareObjectState_scopes_zero_of_cons hsc, ?_⟩
      simpa [hy] using hb

/-- Canonical API: deeper ref bindings are exactly preserved by object declarations. -/
theorem declareObjectState_api_runtimeFrameBindsRef_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k.succ y υ addr ↔
      runtimeFrameBindsRef σ k.succ y υ addr := by
  constructor
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectState_api_succ_scope_iff).1 hfr, hb⟩
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectState_api_succ_scope_iff).2 hfr, hb⟩

/-- Canonical API: old top ref bindings whose name is not `x` are preserved. -/
theorem declareObjectState_api_runtimeFrameBindsRef_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (href : runtimeFrameBindsRef σ 0 y υ addr) :
    runtimeFrameBindsRef (declareObjectState σ τ x ov) 0 y υ addr := by
  rcases href with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      exact ⟨_, declareObjectState_scopes_zero_of_cons hsc, by simpa [hy] using hb⟩

theorem runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ addr := by
  intro href
  cases k with
  | zero =>
      rcases href with ⟨fr, hfr, hb⟩
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hfr
      | cons fr0 frs =>
          simp [hsc] at hfr
          subst fr
          have hy : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh hfresh hsc hb
          exact
            declareObjectState_api_runtimeFrameBindsRef_zero_preserved_of_ne
              hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact (declareObjectState_api_runtimeFrameBindsRef_succ_iff).2 href

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
  intro ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          -- 中間関数をすべて指定して展開し、fr の中身を特定する
          simp [declareObjectState, declareObjectStateWithNext, declareObjectStateCore, bindTopBinding, hsc] at hk
          subst fr
          -- この時点で hb : (if y = x then some (.object τ σ.next) else none) = some (.object υ addr)
          simp at hb
          left
          -- k=0, y=x, υ=τ, addr=σ.next を hb から導出
          simp_all
      | cons fr0 frs =>
          -- 作成済みの補題で fr を特定
          rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hyx : y = x
          · left
            simp_all -- k=0, y=x, 中身の一致を解決
          · right
            exact ⟨fr0, by simp [hsc], by simpa [hyx] using hb⟩
  | succ k =>
      -- 深い階層は不変
      right
      exact ⟨fr, declareObjectState_lookup_succ_iff.1 hk, hb⟩

theorem runtimeFrameBindsRef_declareObjectState_backward
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ addr →
    runtimeFrameBindsRef σ k y υ addr := by
  intro ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          -- nilケースの展開
          simp [declareObjectState, declareObjectStateWithNext, declareObjectStateCore, bindTopBinding, hsc] at hk
          subst fr
          -- hb は (if y = x then some (.object ...) else none) = some (.ref ...)
          -- y=x でも y≠x でも矛盾することを simp が見抜く
          simp at hb
      | cons fr0 frs =>
          rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hyx : y = x
          · subst hyx
            -- 今度は .object と .ref の型の不一致で矛盾
            simp at hb
          · -- 名前が違えば元のフレームにあったはず
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hyx] using hb
  | succ k =>
      -- 深い階層は不変（既存の補題を使用）
      exact ⟨fr, (declareObjectState_api_succ_scope_iff).1 hk, hb⟩

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
      -- zero_cases の結果をそのままパターンマッチで分解
      rcases declareObjectState_api_runtimeFrameOwnsAddress_zero_cases hown with hnew | hold
      · left
        exact ⟨rfl, hnew⟩
      · right
        exact hold
  | succ k =>
      right
      exact (declareObjectState_api_runtimeFrameOwnsAddress_succ_iff).1 hown

theorem runtimeFrameBindsObject_declareObjectState_zero_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next := by
  refine ⟨fr, hk, ?_⟩
  cases hsc : σ.scopes with
  | nil =>
      -- 全展開して hk と矛盾させないように fr を特定する
      simp [declareObjectState, declareObjectStateWithNext, declareObjectStateCore, bindTopBinding, hsc] at hk
      subst fr
      simp
  | cons fr0 frs =>
      -- 既存の cons 用補題で fr を特定
      rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
      simp

theorem declareObjectState_api_runtimeFrameBindsObject_top_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next := by
  cases hsc : σ.scopes with
  | nil =>
      have hk := declareObjectState_scopes_zero_of_nil
        (σ := σ) (τ := τ) (x := x) (ov := ov) hsc
      exact runtimeFrameBindsObject_declareObjectState_zero_new
        (σ := σ) (τ := τ) (x := x) (ov := ov) hk
  | cons fr0 frs =>
      have hk := declareObjectState_scopes_zero_of_cons
        (σ := σ) (τ := τ) (x := x) (ov := ov)
        (fr0 := fr0) (frs := frs) hsc
      exact runtimeFrameBindsObject_declareObjectState_zero_new
        (σ := σ) (τ := τ) (x := x) (ov := ov) hk


/-- Canonical API: old top object bindings whose name is not `x` are preserved by
`declareObjectStateWithNext`.  The allocated object address is still `σ.next`;
`aNext` is only the post-state cursor. -/

theorem declareObjectStateWithNext_api_runtimeFrameBindsObject_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (hobj : runtimeFrameBindsObject σ 0 y υ addr) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 y υ addr := by
  rcases hobj with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      refine ⟨_, declareObjectStateWithNext_scopes_zero_of_cons hsc, ?_⟩
      simpa [hy] using hb


/-- Canonical API: deeper object bindings are exactly preserved by
`declareObjectStateWithNext`. -/

theorem declareObjectStateWithNext_api_runtimeFrameBindsObject_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) k.succ y υ addr ↔
      runtimeFrameBindsObject σ k.succ y υ addr := by
  constructor
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).1 hfr, hb⟩
  · intro hobj
    rcases hobj with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).2 hfr, hb⟩


/-- Canonical API: `declareObjectStateWithNext` binds the newly declared object
in the top frame.  The object address is `σ.next`, not `aNext`. -/

theorem declareObjectStateWithNext_api_runtimeFrameBindsObject_top_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat} :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 x τ σ.next := by
  cases hsc : σ.scopes with
  | nil =>
      refine ⟨_, declareObjectStateWithNext_scopes_zero_of_nil hsc, ?_⟩
      simp
  | cons fr0 frs =>
      refine ⟨_, declareObjectStateWithNext_scopes_zero_of_cons hsc, ?_⟩
      simp


/-- Runtime object bindings after `declareObjectStateWithNext` are either the new
payload binding or an old binding. -/

theorem runtimeFrameBindsObject_declareObjectStateWithNext_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) k y υ addr →
      (k = 0 ∧ y = x ∧ υ = τ ∧ addr = σ.next) ∨
      runtimeFrameBindsObject σ k y υ addr := by
  intro hobj
  rcases hobj with ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_nil hsc hk with rfl
          by_cases hyx : y = x
          · left
            simp_all
          · simp [hyx, emptyScopeFrame] at hb
      | cons fr0 frs =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hyx : y = x
          · left
            simp_all
          · right
            exact ⟨fr0, by simp [hsc], by simpa [hyx] using hb⟩
  | succ k =>
      right
      exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).1 hk, hb⟩


/-- Old object bindings are transported through `declareObjectStateWithNext` when
there is no top-frame name collision. -/
theorem runtimeFrameBindsObject_declareObjectStateWithNext_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsObject σ k y υ addr →
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) k y υ addr := by
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
            declareObjectStateWithNext_api_runtimeFrameBindsObject_zero_preserved_of_ne
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact
        (declareObjectStateWithNext_api_runtimeFrameBindsObject_succ_iff
          (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)).2 hobj

/-- Canonical API: old top ref bindings whose name is not `x` are preserved by
`declareObjectStateWithNext`. -/

theorem declareObjectStateWithNext_api_runtimeFrameBindsRef_zero_preserved_of_ne
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {addr : Nat}
    (hy : y ≠ x)
    (href : runtimeFrameBindsRef σ 0 y υ addr) :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) 0 y υ addr := by
  rcases href with ⟨fr, hfr, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [hsc] at hfr
  | cons fr0 frs =>
      simp [hsc] at hfr
      subst fr
      exact ⟨_, declareObjectStateWithNext_scopes_zero_of_cons hsc, by simpa [hy] using hb⟩


/-- Canonical API: deeper ref bindings are exactly preserved by
`declareObjectStateWithNext`. -/

theorem declareObjectStateWithNext_api_runtimeFrameBindsRef_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) k.succ y υ addr ↔
      runtimeFrameBindsRef σ k.succ y υ addr := by
  constructor
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).1 hfr, hb⟩
  · intro href
    rcases href with ⟨fr, hfr, hb⟩
    exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).2 hfr, hb⟩


/-- Object declaration with a recomputed cursor does not create ref bindings. -/

theorem runtimeFrameBindsRef_declareObjectStateWithNext_backward
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) k y υ addr →
    runtimeFrameBindsRef σ k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_nil hsc hk with rfl
          by_cases hyx : y = x
          · subst y
            simp at hb
          · simp [hyx, emptyScopeFrame] at hb
      | cons fr0 frs =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_cons hsc hk with rfl
          by_cases hyx : y = x
          · subst y
            simp at hb
          · exact ⟨fr0, by simp [hsc], by simpa [hyx] using hb⟩
  | succ k =>
      exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).1 hk, hb⟩


/-- Old ref bindings are transported through `declareObjectStateWithNext` when
there is no top-frame name collision. -/

theorem runtimeFrameBindsRef_declareObjectStateWithNext_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) k y υ addr := by
  intro href
  cases k with
  | zero =>
      rcases href with ⟨fr, hfr, hb⟩
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hfr
      | cons fr0 frs =>
          simp [hsc] at hfr
          subst fr
          have hy : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh hfresh hsc hb
          exact
            declareObjectStateWithNext_api_runtimeFrameBindsRef_zero_preserved_of_ne
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              hy ⟨fr0, by simp [hsc], hb⟩
  | succ k =>
      exact
        (declareObjectStateWithNext_api_runtimeFrameBindsRef_succ_iff
          (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)).2 href


/-- The newly declared object is owned by the top frame after
`declareObjectStateWithNext`.  The owned address is `σ.next`, not `aNext`. -/

theorem declareObjectStateWithNext_api_runtimeFrameOwnsAddress_zero_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat} :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 σ.next := by
  cases hsc : σ.scopes with
  | nil =>
      refine ⟨_, declareObjectStateWithNext_scopes_zero_of_nil hsc, ?_⟩
      simp
  | cons fr0 frs =>
      refine ⟨_, declareObjectStateWithNext_scopes_zero_of_cons hsc, ?_⟩
      simp


/-- Old ownership is transported through `declareObjectStateWithNext`. -/

theorem runtimeFrameOwnsAddress_declareObjectStateWithNext_forward
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress σ k addr →
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) k addr := by
  intro hown
  rcases hown with ⟨fr, hk, hmem⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hk
      | cons fr0 frs =>
          simp [hsc] at hk
          subst fr
          exact ⟨_, declareObjectStateWithNext_scopes_zero_of_cons hsc, by simp [hmem]⟩
  | succ k =>
      exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).2 hk, hmem⟩


/-- Ownership after `declareObjectStateWithNext` is either the new payload owner
or old ownership. -/

theorem runtimeFrameOwnsAddress_declareObjectStateWithNext_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {addr : Nat} :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) k addr →
      (k = 0 ∧ addr = σ.next) ∨ runtimeFrameOwnsAddress σ k addr := by
  intro hown
  rcases hown with ⟨fr, hk, hmem⟩
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_nil hsc hk with rfl
          simp at hmem
          subst addr
          left
          exact ⟨rfl, rfl⟩
      | cons fr0 frs =>
          rcases declareObjectStateWithNext_lookup_zero_frame_of_cons hsc hk with rfl
          simp at hmem
          rcases hmem with hnew | hold
          · subst addr
            left
            exact ⟨rfl, rfl⟩
          · right
            exact ⟨fr0, by simp [hsc], hold⟩
  | succ k =>
      right
      exact ⟨fr, (declareObjectStateWithNext_lookup_succ_iff).1 hk, hmem⟩


/-- All object bindings remain owned after `declareObjectStateWithNext`. -/
theorem allObjectBindingsOwned_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (howned : allObjectBindingsOwned σ) :
    allObjectBindingsOwned (declareObjectStateWithNext σ τ x ov aNext) := by
  intro k y υ addr hobj_new
  rcases runtimeFrameBindsObject_declareObjectStateWithNext_cases hobj_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl, rfl, rfl⟩
    exact declareObjectStateWithNext_api_runtimeFrameOwnsAddress_zero_new
  · exact runtimeFrameOwnsAddress_declareObjectStateWithNext_forward (howned k y υ addr hold)

/-- Owned addresses remain named after `declareObjectStateWithNext`. -/
theorem allOwnedAddressesNamed_declareObjectStateWithNext_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    allOwnedAddressesNamed (declareObjectStateWithNext σ τ x ov aNext) := by
  intro k addr hown_new
  rcases runtimeFrameOwnsAddress_declareObjectStateWithNext_cases hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact ⟨x, τ, declareObjectStateWithNext_api_runtimeFrameBindsObject_top_new⟩
  · rcases hnamed k addr hold with ⟨y, υ, hobj_old⟩
    exact ⟨y, υ,
      runtimeFrameBindsObject_declareObjectStateWithNext_forward_of_topFresh hfresh hobj_old⟩

/-- Ref bindings are never owned after `declareObjectStateWithNext`, assuming the
old naming invariant and top-frame freshness. -/
theorem refBindingsNeverOwned_declareObjectStateWithNext_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    refBindingsNeverOwned (declareObjectStateWithNext σ τ x ov aNext) := by
  intro k fr y υ addr hk href hmem
  have hown_new : runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) k addr :=
    ⟨fr, hk, hmem⟩
  rcases runtimeFrameOwnsAddress_declareObjectStateWithNext_cases hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    rcases declareObjectStateWithNext_api_runtimeFrameBindsObject_top_new
      (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext) with
      ⟨fr', hk', hb'⟩
    have heq : fr = fr' := lookup_some_frame_eq hk hk'
    subst fr'
    exact ⟨x, τ, hb'⟩
  · rcases hnamed k addr hold with ⟨z, β, hobj_old⟩
    rcases runtimeFrameBindsObject_declareObjectStateWithNext_forward_of_topFresh
      (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
      hfresh hobj_old with ⟨fr', hk', hb'⟩
    have heq : fr = fr' := lookup_some_frame_eq hk hk'
    subst fr'
    exact ⟨z, β, hb'⟩

/-- Inner-owned avoidance is preserved by `declareObjectStateWithNext` when no
inner ref targets the fresh payload address `σ.next`. -/
theorem refTargetsAvoidInnerOwned_declareObjectStateWithNext_of_noInnerNextAlias
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (havoid : ∀ {k y υ a j}, runtimeFrameBindsRef σ k y υ a → j < k → ¬ runtimeFrameOwnsAddress σ j a)
    (hnoNext : nextNotTargetOfInnerRefs σ) :
    ∀ {k y υ a j},
      runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) j a := by
  intro k y υ a j href_new hjk hown_new
  have href_old := runtimeFrameBindsRef_declareObjectStateWithNext_backward href_new
  rcases runtimeFrameOwnsAddress_declareObjectStateWithNext_cases hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    cases k with
    | zero => exact Nat.not_lt_zero _ hjk
    | succ k =>
        exact hnoNext (Nat.succ_pos k) href_old
  · exact havoid href_old hjk hold

/-- Per-frame ownership no-dup is preserved by `declareObjectStateWithNext`. -/
theorem ownedAddressesNoDupPerFrame_declareObjectStateWithNext_of_nextFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat} :
    ownedAddressesNoDupPerFrame σ →
    nextFreshAgainstOwned σ →
    ownedAddressesNoDupPerFrame (declareObjectStateWithNext σ τ x ov aNext) := by
  intro hnodup hfresh
  have hold : ownedAddressesNoDupPerFrame (declareObjectState σ τ x ov) :=
    ownedAddressesNoDupPerFrame_declareObjectState_of_nextFresh
      (σ := σ) (τ := τ) (x := x) (ov := ov) hnodup hfresh
  intro k fr hk
  exact hold k fr (by
    simpa [scopes_declareObjectStateWithNext_eq_declareObjectState] using hk)

/-- Backward-compatible name. -/
 theorem runtimeFrameBindsObject_declareObjectState_new
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next := by
  exact runtimeFrameBindsObject_declareObjectState_zero_new hk

 theorem allObjectBindingsOwned_declareObjectState
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (howned : allObjectBindingsOwned σ) :
    allObjectBindingsOwned (declareObjectState σ τ x ov) := by
  intro k y υ addr hobj_new
  rcases runtimeFrameBindsObject_declareObjectState_cases hobj_new with hnew | hold
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
  rcases runtimeFrameOwnsAddress_declareObjectState_cases hown_new with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    rcases hown_new with ⟨fr, hk, _hmem⟩
    exact ⟨x, τ, runtimeFrameBindsObject_declareObjectState_zero_new hk⟩
  · rcases hnamed k addr hold with ⟨y, υ, hobj_old⟩
    exact ⟨y, υ, runtimeFrameBindsObject_declareObjectState_forward_of_topFresh hfresh hobj_old⟩

theorem refBindingsNeverOwned_declareObjectState_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hnamed : allOwnedAddressesNamed σ)
    (hfresh : topFrameBindingFresh σ x) :
    refBindingsNeverOwned (declareObjectState σ τ x ov) := by
  intro k fr y υ addr hk href hmem
  -- 1. このアドレスが「新入り」か「古株」かを判定
  have hown_new : runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k addr := ⟨fr, hk, hmem⟩
  rcases runtimeFrameOwnsAddress_declareObjectState_cases hown_new with ⟨rfl, rfl⟩ | hold
  · -- ケース1: 今宣言されたオブジェクトのアドレス (σ.next) だった場合
    -- zero_new 補題で、そのアドレスが x にバインドされていることを示す
    rcases runtimeFrameBindsObject_declareObjectState_zero_new hk with ⟨fr', hk', hb'⟩
    -- フレームの一致を確認して終了
    have : fr = fr' := lookup_some_frame_eq hk hk'
    subst fr'
    exact ⟨x, τ, hb'⟩
  · -- ケース2: 元から所有されていたアドレスだった場合
    -- hnamed で元の状態での Object バインディングを取得
    rcases hnamed k addr hold with ⟨z, β, hobj_old⟩
    -- forward 補題で、新しい状態でもそのバインディングが維持されていることを示す
    rcases runtimeFrameBindsObject_declareObjectState_forward_of_topFresh hfresh hobj_old with ⟨fr', hk', hb'⟩
    -- フレームの一致を確認して終了
    have : fr = fr' := lookup_some_frame_eq hk hk'
    subst fr'
    exact ⟨z, β, hb'⟩

theorem refTargetsAvoidInnerOwned_declareObjectState_of_noInnerNextAlias
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (havoid : ∀ {k y υ a j}, runtimeFrameBindsRef σ k y υ a → j < k → ¬ runtimeFrameOwnsAddress σ j a)
    (hnoNext : nextNotTargetOfInnerRefs σ) :
    ∀ {k y υ a j},
      runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress (declareObjectState σ τ x ov) j a := by
  intro k y υ a j href_new hjk hown_new
  -- 1. 新しい状態での参照は、元からあった参照である (Object宣言はRefを増やさないため)
  have href_old := runtimeFrameBindsRef_declareObjectState_backward href_new
  -- 2. 新しい状態での所有アドレスが「新入り」か「古株」かで分ける
  rcases runtimeFrameOwnsAddress_declareObjectState_cases hown_new with ⟨hj0, ha_next⟩ | hold
  · -- ケース1: a = σ.next (新しく作られたオブジェクト) の場合
    subst j a
    -- 「σ.next はどの内側の参照からも指されていない」という仮定 (hnoNext) より矛盾
    exact hnoNext hjk href_old
  · -- ケース2: a が元から所有されていた場合
    -- 「元の状態で内側を指していない」という仮定 (havoid) より矛盾
    exact havoid href_old hjk hold

end DeclareObjectStateOwnershipTransport

end Cpp
