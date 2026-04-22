import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalEnvExtending
import CppFormalization.Cpp2.Lemmas.TypeEnv

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalEnvExtendingNames

Old-name / fresh-name lookup layer for env-extending normal heads.

The next real proof step after `ReadinessTransportNormalEnvExtending` is not yet
full readiness transport. First we need theorem-backed control over the *name
split* created by declaration heads:

- the fresh name `x` is visible in the post environment with exactly the newly
  introduced declaration shape;
- all old names `y ≠ x` are looked up exactly as before;
- top-scope freshness behaves correspondingly.

This file isolates that lookup algebra so later place / expr / stmt / block
transport proofs can split cleanly into

- fresh-name case
- old-name case

without re-proving environment facts each time.
-/

--補題をたくさん追加したからあとから整理が必要
/- =========================================================
   1. exact lookup behavior for declaration heads
   ========================================================= -/

theorem declareObj_lookup_self
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
  simp

theorem declareRef_lookup_self
    {Γ : TypeEnv} {x : Ident} {τ : CppType}:
    lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
  simp

theorem declareObj_lookup_other
    {Γ : TypeEnv} {x y : Ident} {τ : CppType} :
    y ≠ x →
    lookupDecl (declareTypeObject Γ x τ) y = lookupDecl Γ y := by
  intro hxy
  simp [lookupDecl_declareTypeObject_other, hxy]

theorem declareRef_lookup_other
    {Γ : TypeEnv} {x y : Ident} {τ : CppType}  :
    y ≠ x →
    lookupDecl (declareTypeRef Γ x τ) y = lookupDecl Γ y := by
  intro hxy
  simp [lookupDecl_declareTypeRef_other, hxy]

-- 更新したキーそのものを引いた場合
theorem lookup_update_eq (f : Ident → Option DeclInfo) (x : Ident) (d : DeclInfo) :
  (fun y => if y = x then some d else f y) x = some d := by
  simp

-- 更新したキーとは別のキーを引いた場合
theorem lookup_update_ne (f : Ident → Option DeclInfo) (x y : Ident) (d : DeclInfo) :
  y ≠ x → (fun z => if z = x then some d else f z) y = f y := by
  intro hne
  simp [hne]

def updateFrame (fr : TypeFrame) (x : Ident) (d : DeclInfo) : TypeFrame :=
  { decls := fun y => if y = x then some d else fr.decls y }

theorem lookup_frame_update_eq (fr : TypeFrame) (x : Ident) (d : DeclInfo) :
  (updateFrame fr x d).decls x = some d :=
  lookup_update_eq fr.decls x d

theorem lookup_frame_update_ne (fr : TypeFrame) (x y : Ident) (d : DeclInfo) (h : y ≠ x) :
  (updateFrame fr x d).decls y = fr.decls y :=
  lookup_update_ne fr.decls x y d h

-- 同じ名前で上書きしても、最新のものが優先されることの確認
theorem declareObj_shadowing
    {Γ : TypeEnv} {x : Ident} {τ1 τ2 : CppType} :
    lookupDecl (declareTypeObject (declareTypeObject Γ x τ1) x τ2) x = some (.object τ2) := by
  simp



theorem lookup_weakening {Γ : TypeEnv} {x y : Ident} {τ τ_y : CppType} :
  y ≠ x →
  lookupDecl Γ y = some (.object τ_y) →
  lookupDecl (declareTypeObject Γ x τ) y = some (.object τ_y) := by
  intro hne hlook
  rw [declareObj_lookup_other hne]
  exact hlook

theorem lookup_push_shadowing (Γ : TypeEnv) (x : Ident) (d : DeclInfo) :
  lookupDecl (insertTopDecl (pushTypeScope Γ) x d) x = some d := by
  simp [pushTypeScope, insertTopDecl, lookupDecl, lookupDeclFrames]

theorem lookup_lower_frames (fr : TypeFrame) (frs : List TypeFrame) (x y : Ident) (d : DeclInfo) :
  y ≠ x →
  lookupDeclFrames (fr :: frs) y =
  lookupDeclFrames ({ fr with decls := fun z => if z = x then some d else fr.decls z } :: frs) y := by
  intro hne
  -- lookupDeclFrames の定義を展開
  simp [lookupDeclFrames]
  -- if-then-else の条件 (y = x) を評価
  rw [if_neg hne]

theorem lookup_in_deeper_frames (fr : TypeFrame) (frs : List TypeFrame) (x y : Ident) (d : DeclInfo) :
  y ≠ x →
  fr.decls y = none →
  lookupDeclFrames ({ fr with decls := fun z => if z = x then some d else fr.decls z } :: frs) y =
  lookupDeclFrames frs y := by
  intro hne hfresh
  simp [lookupDeclFrames, hne, hfresh]

-- y ≠ x のとき、insertTopDecl をしても既存のスコープの結果は変わらないという補題
theorem lookupDeclFrames_insertTopDecl_other
    (fr : TypeFrame) (frs : List TypeFrame) (x y : Ident) (d : DeclInfo) :
    y ≠ x →
    lookupDeclFrames ({ fr with decls := fun z => if z = x then some d else fr.decls z } :: frs) y =
    lookupDeclFrames (fr :: frs) y := by
  intro hne
  simp [lookupDeclFrames]
  -- y ≠ x なので、if-then-else は else 側 (fr.decls y) に簡約される
  simp [hne]

theorem declareObj_lookup_other_full
    {Γ : TypeEnv} {x y : Ident} {τ : CppType} (hne : y ≠ x) :
    lookupDecl (declareTypeObject Γ x τ) y = lookupDecl Γ y := by
  unfold declareTypeObject insertTopDecl lookupDecl
  cases Γ.scopes with
  | nil =>
    simp [lookupDeclFrames, hne]
  | cons fr frs =>
    simp [lookupDeclFrames, hne]

theorem lookup_push_fresh (Γ : TypeEnv) (x : Ident) :
  (pushTypeScope Γ).scopes.head?.bind (·.decls x) = none := by
  simp [pushTypeScope, emptyTypeFrame]

-- より実用的な形：新しいスコープで定義されていないなら、lookup の結果は変わらない
theorem lookup_push_invariant (Γ : TypeEnv) (x : Ident) :
  lookupDecl (pushTypeScope Γ) x = lookupDecl Γ x := by
  simp [pushTypeScope, lookupDecl, lookupDeclFrames, emptyTypeFrame]

def popTypeScope (Γ : TypeEnv) : TypeEnv :=
  { Γ with scopes := Γ.scopes.tail }

theorem lookup_pop_invariant (Γ : TypeEnv) (x : Ident) (d : DeclInfo) :
  -- push して何かを宣言 (insertTopDecl) しても、pop すれば元の Γ と等しくなる
  popTypeScope (insertTopDecl (pushTypeScope Γ) x d) = Γ := by
  simp [popTypeScope, insertTopDecl, pushTypeScope]
  -- List.tail (fr :: frs) = frs の性質で証明終了

theorem lookup_none_preserved {Γ : TypeEnv} {x y : Ident} {τ : CppType} :
    lookupDecl (declareTypeObject Γ x τ) y = none → lookupDecl Γ y = none := by
  intro h
  by_cases hne : y = x
  · -- y = x の場合
    subst hne
    -- lookupDecl (... x ...) x は some (.object τ) なので、
    -- lookupDecl (...) x = none という仮定 h と矛盾する
    simp at h
  · -- y ≠ x の場合
    -- declareObj_lookup_other を使って書き換え
    rw [declareObj_lookup_other hne] at h
    exact h

-- push した直後の lookup は、
-- 1. トップレベルのフレームにあるか
-- 2. なければそれ以降のフレーム（元の環境）にあるか
-- のいずれかであることの証明
theorem lookup_push_spec (Γ : TypeEnv) (x : Ident) (fr : TypeFrame) :
    lookupDecl { scopes := fr :: Γ.scopes } x =
    (fr.decls x).or (lookupDecl Γ x) := by
  simp [lookupDecl, lookupDeclFrames]
  -- fr.decls x の中身で場合分け
  cases fr.decls x with
  | none =>
      -- 両辺ともに lookupDeclFrames Γ.scopes x になる
      simp
  | some d =>
      -- 両辺ともに some d になる
      simp

/- =========================================================
   2. top-scope freshness behavior
   ========================================================= -/
--抽象的
theorem currentTypeScopeFresh_insertTopDecl_false
    (Γ : TypeEnv) (x : Ident) (d : DeclInfo) :
    ¬ currentTypeScopeFresh (insertTopDecl Γ x d) x := by
  intro h
  cases hsc : Γ.scopes with
  | nil =>
      -- Γ.scopes が [] であることを h に教え込む
      unfold insertTopDecl currentTypeScopeFresh at h
      rw [hsc] at h
      simp at h
  | cons fr frs =>
      -- Γ.scopes が fr :: frs であることを h に教え込む
      unfold insertTopDecl currentTypeScopeFresh at h
      rw [hsc] at h
      simp at h


-- Object版の個別定理
theorem currentTypeScopeFresh_declareObj_self_false
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    ¬ currentTypeScopeFresh (declareTypeObject Γ x τ) x :=
  currentTypeScopeFresh_insertTopDecl_false Γ x (.object τ)

-- Ref版の個別定理
theorem currentTypeScopeFresh_declareRef_self_false
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    ¬ currentTypeScopeFresh (declareTypeRef Γ x τ ) x :=
  currentTypeScopeFresh_insertTopDecl_false Γ x (.ref τ)

--Γが空ではないという前提
def TypeEnvNonempty (Γ : TypeEnv) : Prop := Γ.scopes ≠ []

theorem currentTypeScopeFresh_insertTopDecl_other_iff
    (Γ : TypeEnv) (x y : Ident) (d : DeclInfo) (hne : y ≠ x)
    (h_nonempty : TypeEnvNonempty Γ) :
    currentTypeScopeFresh (insertTopDecl Γ x d) y ↔ currentTypeScopeFresh Γ y := by
  unfold currentTypeScopeFresh insertTopDecl
  -- Γ.scopes の形状で場合分け
  cases hsc : Γ.scopes with
  | nil =>
      -- Γ.scopes = [] は TypeEnvNonempty Γ に矛盾する
      exact (h_nonempty hsc).elim
  | cons fr frs =>
      -- 両辺ともにスコープが存在する状態。y ≠ x なので if が else 側に簡約される
      simp [hne]

theorem currentTypeScopeFresh_declareObj_other_iff
    {Γ : TypeEnv} {x y : Ident} {τ : CppType}
    (h_nonempty : TypeEnvNonempty Γ) (hne : y ≠ x) :
    currentTypeScopeFresh (declareTypeObject Γ x τ) y ↔ currentTypeScopeFresh Γ y :=
  currentTypeScopeFresh_insertTopDecl_other_iff Γ x y (.object τ) hne h_nonempty

theorem currentTypeScopeFresh_declareRef_other_iff
    {Γ : TypeEnv} {x y : Ident} {τ : CppType}
    (h_nonempty : TypeEnvNonempty Γ) (hne : y ≠ x) :
    currentTypeScopeFresh (declareTypeRef Γ x τ ) y ↔ currentTypeScopeFresh Γ y :=
  currentTypeScopeFresh_insertTopDecl_other_iff Γ x y (.ref τ) hne h_nonempty


/- =========================================================
   3. ctx-level lookup consequences
   ========================================================= -/

theorem env_extending_ctx_lookup_self
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    EnvExtendingNormalHead head →
    NormalTransportCtx Γ Δ σ σ' head →
      (∃ x τ, Δ = declareTypeObject Γ x τ ∧ lookupDecl Δ x = some (.object τ)) ∨
      (∃ x τ, Δ = declareTypeRef Γ x τ ∧ lookupDecl Δ x = some (.ref τ)) := by
  intro hhead hctx
  rcases env_extending_normal_ctx_post_env_shape hhead hctx with hshape
  cases hshape with
  | inl hobj =>
      rcases hobj with ⟨x, τ, hΔ⟩
      left
      refine ⟨x, τ, hΔ, ?_⟩
      subst hΔ
      simp
  | inr href =>
      rcases href with ⟨x, τ, hΔ⟩
      right
      refine ⟨x, τ, hΔ, ?_⟩
      subst hΔ
      simp

theorem env_extending_ctx_lookup_other
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} {x y : Ident} :
    EnvExtendingNormalHead head →
    y ≠ x →
    NormalTransportCtx Γ Δ σ σ' head →
      ((∃ τ ov, head = .declareObj τ x ov) → lookupDecl Δ y = lookupDecl Γ y) ∧
      ((∃ τ p, head = .declareRef τ x p) → lookupDecl Δ y = lookupDecl Γ y) := by
  intro hhead hxy hctx
  constructor
  · intro hobj
    rcases hobj with ⟨τ, ov, rfl⟩
    have h_env : Δ = declareTypeObject Γ x τ := by
      cases hctx with
      | mk hty _ hpost =>
          cases ov with
          | none =>
              rcases declareObjNone_post_env_data hty with ⟨_, _, hΔ⟩
              exact hΔ
          | some e =>
              rcases declareObjSome_post_env_data hty with ⟨_, _, _, hΔ⟩
              exact hΔ
    subst h_env
    exact declareObj_lookup_other hxy

  · intro href
    rcases href with ⟨τ, p, rfl⟩
    have h_env : Δ = declareTypeRef Γ x τ := by
      cases hctx with
      | mk hty _ hpost =>
          rcases declareRef_post_env_data hty with ⟨_, _, hΔ⟩
          exact hΔ
    subst h_env
    exact declareRef_lookup_other hxy


end Cpp
