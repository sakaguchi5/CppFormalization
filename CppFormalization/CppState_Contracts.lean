import CppFormalization.CppState

namespace Cpp

/-
追加契約層。

狙い:
1. State 操作の exact contract を固定する。
2. declaration / write / exitScope の postcondition を使いやすい形に切り出す。
3. 現行の WF (= key 一意性ベース) が保たれる範囲を明示する。

注意:
- ここで扱う WF は現在の `State.WF` / `Env.WF` / `Store.WF` に対するもの。
- `nextLoc` の真の freshness や `Cell.ty` と `Cell.object` の整合性まではまだ含まない。
-/

-- ============================================================
-- §1. Assoc / Store helper lemmas
-- ============================================================

namespace Assoc

 theorem lookup_upsert_eq
    [BEq α] [LawfulBEq α]
    (m : Map α β) (x : α) (v : β) :
    lookup (upsert m x v) x = some v := by
  induction m with
  | nil =>
      simp [lookup, upsert]
  | cons kv xs ih =>
      rcases kv with ⟨k, w⟩
      by_cases h : k == x
      · simp [lookup, upsert, h]
      · simp [lookup, upsert, h, ih]

 theorem modify?_eq_some_upsert_of_lookup_some
    [BEq α] [LawfulBEq α]
    (m : Map α β) (x : α) (f : β → β) (v : β)
    (h : lookup m x = some v) :
    modify? m x f = some (upsert m x (f v)) := by
  induction m with
  | nil =>
      simp [lookup] at h
  | cons kv xs ih =>
      rcases kv with ⟨k, w⟩
      by_cases hk : k == x
      · have hkx : k = x := by
          simpa using hk
        simp [lookup, hk] at h
        subst h
        subst hkx
        simp [modify?, upsert]
      · simp [lookup, hk] at h
        have ih' := ih h
        simp [modify?, upsert, hk, ih']
--「keys については head の k が残り、再帰側から x が来るので、
--論理式が k ∨ x ∨ rest と x ∨ k ∨ rest の違いだけになる
private theorem or_left_comm_3 {A B C : Prop} :
    A ∨ B ∨ C ↔ B ∨ A ∨ C := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

 theorem mem_keys_upsert_iff
    [BEq α] [LawfulBEq α]
    (m : Map α β) (x y : α) (v : β) :
    y ∈ keys (upsert m x v) ↔ y = x ∨ y ∈ keys m := by
  induction m with
  | nil =>
      simp [upsert, keys]
  | cons kv xs ih =>
      rcases kv with ⟨k, w⟩
      by_cases hk : (k == x) = true
      · have hkx : k = x := by
          simpa using hk
        subst hkx
        simp [upsert, keys]
      · simp [upsert, hk, keys, ih]
        simp [or_left_comm_3]

theorem NoDupKeys_upsert
    [BEq α] [LawfulBEq α] [DecidableEq α]
    {m : Map α β} (h : NoDupKeys m) (x : α) (v : β) :
    NoDupKeys (upsert m x v) := by
  induction m with
  | nil =>
      simp [NoDupKeys, upsert, keys]
  | cons kv xs ih =>
      rcases kv with ⟨k, w⟩
      have hnd : List.Nodup (k :: keys xs) := by
        simpa [NoDupKeys, keys] using h
      have hk_notin_xs : k ∉ keys xs := (List.nodup_cons.mp hnd).1
      have hxs : NoDupKeys xs := by
        simpa [NoDupKeys, keys] using (List.nodup_cons.mp hnd).2
      by_cases hk : (k == x) = true
      · have hkx : k = x := by
          simpa using hk
        subst hkx
        simpa [NoDupKeys, upsert, keys] using h
      · have hrec : NoDupKeys (upsert xs x v) := ih hxs
        have hk_notin_upsert : k ∉ keys (upsert xs x v) := by
          intro hmem
          have hmem' : k = x ∨ k ∈ keys xs :=
            (mem_keys_upsert_iff xs x k v).1 hmem
          rcases hmem' with hEq | hIn
          · have : (k == x) = true := by
              simp [hEq]
            exact hk this
          · exact hk_notin_xs hIn
        have hnd_upsert : List.Nodup (k :: keys (upsert xs x v)) := by
          exact List.nodup_cons.mpr ⟨hk_notin_upsert, by
            simpa [NoDupKeys, keys] using hrec⟩
        simpa [NoDupKeys, upsert, keys, hk] using hnd_upsert

theorem keys_modify?_some_eq
    [BEq α] [LawfulBEq α]
    (m : Map α β) (x : α) (f : β → β) :
    ∀ (m' : Map α β), modify? m x f = some m' → keys m' = keys m := by
  induction m with
  | nil =>
      intro m' h
      simp [modify?] at h
  | cons kv xs ih =>
      rcases kv with ⟨k, v⟩
      intro m' h
      by_cases hk : k == x
      · simp [modify?, hk] at h
        cases h
        rfl
      · cases hmod : modify? xs x f with
        | none =>
            simp [modify?, hk, hmod] at h
        | some xs' =>
            simp [modify?, hk, hmod] at h
            cases h
            simp [keys, ih xs' hmod]

 theorem NoDupKeys_modify?_some
    [BEq α] [LawfulBEq α] [DecidableEq α]
    {m : Map α β} (hnd : NoDupKeys m) (x : α) (f : β → β) (m' : Map α β)
    (h : modify? m x f = some m') :
    NoDupKeys m' := by
  unfold NoDupKeys at hnd ⊢
  rw [keys_modify?_some_eq m x f m' h]
  exact hnd

end Assoc

namespace Store

 theorem read_write_eq (st : Store) (l : Loc) (c : Cell) :
    read (write st l c) l = some c := by
  simpa [read, write] using Assoc.lookup_upsert_eq st l c

 theorem modify?_eq_some_write_of_read_some
    (st : Store) (l : Loc) (f : Cell → Cell) (c : Cell)
    (h : read st l = some c) :
    modify? st l f = some (write st l (f c)) := by
  simpa [read, write] using
    (Assoc.modify?_eq_some_upsert_of_lookup_some st l f c h)

theorem WF_write
    {st : Store} (h : WF st) (l : Loc) (c : Cell) :
    WF (write st l c) := by
  simpa [WF, write] using Assoc.NoDupKeys_upsert h l c

theorem WF_modify?_some
    {st : Store} (h : WF st) (l : Loc) (f : Cell → Cell) (st' : Store)
    (hm : modify? st l f = some st') :
    WF st' := by
  simpa [WF] using Assoc.NoDupKeys_modify?_some h l f st' hm

 theorem WF_killMany
    [DecidableEq Loc]
    {st : Store} (h : WF st) (ls : List Loc) :
    WF (killMany st ls) := by
  induction ls generalizing st with
  | nil =>
      simpa [killMany] using h
  | cons l rest ih =>
      simp [killMany]
      cases hmod : modify? st l Cell.kill with
      | none =>
          exact ih h
      | some st' =>
          exact ih (WF_modify?_some h l Cell.kill st' hmod)

end Store

namespace Frame

 theorem WF_bind
    {fr : Frame} (h : fr.WF) (x : Ident) (l : Loc) :
    (fr.bind x l).WF := by
  simpa [Frame.WF, Frame.bind] using (Assoc.NoDupKeys_upsert h x l)

theorem WF_own
    {fr : Frame} (h : fr.WF) (l : Loc) :
    (fr.own l).WF := by
  dsimp [Frame.WF] at h ⊢
  by_cases hm : l ∈ fr.owned
  · simp [Frame.own, hm]
    simpa using h
  · simp [Frame.own, hm]
    simpa using h

end Frame

namespace Env

theorem WF_enterScope
    (env : Env) (h : env.WF) :
    (env.enterScope).WF := by
  rcases h with ⟨hg, hls⟩
  refine ⟨hg, ?_⟩
  simp [Env.enterScope]
  constructor
  · simp [Frame.WF, Frame.empty, Assoc.NoDupKeys, Assoc.keys]
  · exact hls

 theorem WF_bindGlobal
    [DecidableEq Ident]
    {env : Env} (h : env.WF) (x : Ident) (l : Loc) :
    (Env.bindGlobal env x l).WF := by
  rcases h with ⟨hg, hls⟩
  exact ⟨Frame.WF_bind hg x l, by simpa [Env.bindGlobal] using hls⟩

 theorem WF_bindCurrentLocal?_some
    [DecidableEq Ident]
    {env env' : Env} (h : env.WF) (x : Ident) (l : Loc)
    (hb : Env.bindCurrentLocal? env x l = some env') :
    env'.WF := by
  cases env with
  | mk global locals =>
      rcases h with ⟨hg, hls⟩
      cases locals with
      | nil =>
          simp [Env.bindCurrentLocal?] at hb
      | cons fr rest =>
          simp [Env.bindCurrentLocal?] at hb
          cases hb
          rcases hls with ⟨hfr, hrest⟩
          exact ⟨hg, by simpa using And.intro (Frame.WF_bind hfr x l) hrest⟩

 theorem WF_ownCurrentLocal?_some
    {env env' : Env} (h : env.WF) (l : Loc)
    (ho : Env.ownCurrentLocal? env l = some env') :
    env'.WF := by
  cases env with
  | mk global locals =>
      rcases h with ⟨hg, hls⟩
      cases locals with
      | nil =>
          simp [Env.ownCurrentLocal?] at ho
      | cons fr rest =>
          simp [Env.ownCurrentLocal?] at ho
          cases ho
          rcases hls with ⟨hfr, hrest⟩
          exact ⟨hg, by simpa using And.intro (Frame.WF_own hfr l) hrest⟩

theorem WF_exitScope_some
    {env : Env} (h : env.WF) (fr : Frame) (env' : Env)
    (he : Env.exitScope env = some (fr, env')) :
    env'.WF := by
  cases env with
  | mk global locals =>
      rcases h with ⟨hg, hls⟩
      cases locals with
      | nil =>
          simp [Env.exitScope] at he
      | cons top rest =>
          simp [Env.exitScope] at he
          rcases hls with ⟨htop, hrest⟩
          rcases he with ⟨rfl, rfl⟩
          exact ⟨hg, hrest⟩

end Env

namespace State

 theorem WF_writeCell
    [DecidableEq Loc]
    {s : State} (h : s.WF) (l : Loc) (c : Cell) :
    (s.writeCell l c).WF := by
  rcases h with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  exact ⟨henv, Store.WF_write hstore l c, hfuncs, hstructs, by simpa [State.writeCell] using hnext⟩

 theorem WF_enterScope
    (s : State) (h : s.WF) :
    (s.enterScope).WF := by
  rcases h with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  exact ⟨Env.WF_enterScope _ henv, by simpa [State.enterScope] using hstore,
    by simpa [State.enterScope] using hfuncs,
    by simpa [State.enterScope] using hstructs,
    by simpa [State.enterScope] using hnext⟩

 theorem WF_bindGlobal
    [DecidableEq Ident]
    {s : State} (h : s.WF) (x : Ident) (l : Loc) :
    (s.bindGlobal x l).WF := by
  rcases h with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  exact ⟨Env.WF_bindGlobal henv x l, by simpa [State.bindGlobal] using hstore,
    by simpa [State.bindGlobal] using hfuncs,
    by simpa [State.bindGlobal] using hstructs,
    by simpa [State.bindGlobal] using hnext⟩

 theorem WF_bindCurrentLocal?_some
    [DecidableEq Ident]
    {s s' : State} (h : s.WF) (x : Ident) (l : Loc)
    (hb : s.bindCurrentLocal? x l = some s') :
    s'.WF := by
  rcases h with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  unfold State.bindCurrentLocal? at hb
  cases henv' : Env.bindCurrentLocal? s.env x l with
  | none => simp [henv'] at hb
  | some env' =>
      simp [henv'] at hb
      cases hb
      exact ⟨Env.WF_bindCurrentLocal?_some henv x l henv', hstore, hfuncs, hstructs, hnext⟩

 theorem WF_ownCurrentLocal?_some
    {s s' : State} (h : s.WF) (l : Loc)
    (ho : s.ownCurrentLocal? l = some s') :
    s'.WF := by
  rcases h with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  unfold State.ownCurrentLocal? at ho
  cases henv' : Env.ownCurrentLocal? s.env l with
  | none => simp [henv'] at ho
  | some env' =>
      simp [henv'] at ho
      cases ho
      exact ⟨Env.WF_ownCurrentLocal?_some henv l henv', hstore, hfuncs, hstructs, hnext⟩

end State

-- ============================================================
-- §2. Exact equations for core operations
-- ============================================================

section ExactContracts

 theorem exitScope_eq (s : State) :
    s.exitScope =
      match Env.exitScope s.env with
      | none => .error .scopeUnderflow s
      | some (fr, env') =>
          .ok PUnit.unit { s with env := env', store := Store.killMany s.store fr.owned } := by
  rfl

 theorem declareGlobalObject_eq
    (s : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    s.declareGlobalObject x ty obj initialized =
      let cell : Cell :=
        { ty := ty, object := obj, storage := .global, initialized := initialized, alive := true }
      let l := s.nextLoc
      .ok l
        { env := Env.bindGlobal s.env x l
        , store := Store.write s.store l cell
        , funcs := s.funcs
        , structs := s.structs
        , nextLoc := s.nextLoc + 1 } := by
  rfl

 theorem allocHeapObject_eq
    (s : State) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    s.allocHeapObject ty obj initialized =
      let cell : Cell :=
        { ty := ty, object := obj, storage := .heap, initialized := initialized, alive := true }
      let l := s.nextLoc
      .ok (.ptr l)
        { env := s.env
        , store := Store.write s.store l cell
        , funcs := s.funcs
        , structs := s.structs
        , nextLoc := s.nextLoc + 1 } := by
  rfl

 theorem declareStackObject_eq
    (s : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    s.declareStackObject x ty obj initialized =
      let cell : Cell :=
        { ty := ty, object := obj, storage := .stack, initialized := initialized, alive := true }
      let l := s.nextLoc
      let s1 : State :=
        { env := s.env
        , store := Store.write s.store l cell
        , funcs := s.funcs
        , structs := s.structs
        , nextLoc := s.nextLoc + 1 }
      match s1.bindCurrentLocal? x l with
      | none => .error .scopeUnderflow s
      | some s2 =>
          match s2.ownCurrentLocal? l with
          | none => .error .scopeUnderflow s
          | some s3 => .ok l s3 := by
  rfl

 theorem writeScalar_invalidLoc
    (s : State) (l : Loc) (v : RValue)
    (hread : s.readCell l = none) :
    s.writeScalar l v = .error (.invalidLoc l) s := by
  unfold State.writeScalar
  rw [hread]

 theorem writeObject_invalidLoc
    (s : State) (l : Loc) (obj : Object)
    (hread : s.readCell l = none) :
    s.writeObject l obj = .error (.invalidLoc l) s := by
  unfold State.writeObject
  rw [hread]

 theorem writeScalar_dead
    (s : State) (l : Loc) (v : RValue) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = false) :
    s.writeScalar l v = .error (.useAfterFree l) s := by
  unfold State.writeScalar
  rw [hread]
  simp [halive]

 theorem writeObject_dead
    (s : State) (l : Loc) (obj : Object) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = false) :
    s.writeObject l obj = .error (.useAfterFree l) s := by
  unfold State.writeObject
  rw [hread]
  simp [halive]

 theorem writeScalar_alive_eq
    (s : State) (l : Loc) (v : RValue) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    s.writeScalar l v =
      .ok PUnit.unit { s with store := Store.write s.store l (c.overwriteScalar v) } := by
  unfold State.writeScalar
  rw [hread]
  simp [halive]
  unfold State.modifyCell?
  have hmodStore :
      Store.modify? s.store l (fun c => c.overwriteScalar v)
        = some (Store.write s.store l (c.overwriteScalar v)) := by
    apply Store.modify?_eq_some_write_of_read_some
    simpa [State.readCell] using hread
  rw [hmodStore]

 theorem writeObject_alive_eq
    (s : State) (l : Loc) (obj : Object) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    s.writeObject l obj =
      .ok PUnit.unit { s with store := Store.write s.store l (c.overwriteObject obj) } := by
  unfold State.writeObject
  rw [hread]
  simp [halive]
  unfold State.modifyCell?
  have hmodStore :
      Store.modify? s.store l (fun c => c.overwriteObject obj)
        = some (Store.write s.store l (c.overwriteObject obj)) := by
    apply Store.modify?_eq_some_write_of_read_some
    simpa [State.readCell] using hread
  rw [hmodStore]

end ExactContracts

-- ============================================================
-- §3. Scope / declaration / write contracts
-- ============================================================

section Contracts

theorem exitScope_success_store_eq
    (s s' : State) (h : s.exitScope = .ok PUnit.unit s') :
    ∃ fr env',
      Env.exitScope s.env = some (fr, env') ∧
      s'.env = env' ∧
      s'.store = Store.killMany s.store fr.owned ∧
      s'.funcs = s.funcs ∧
      s'.structs = s.structs ∧
      s'.nextLoc = s.nextLoc := by
  unfold State.exitScope at h
  cases henv : Env.exitScope s.env with
  | none =>
      simp [henv] at h
  | some p =>
      cases p with
      | mk fr env' =>
          simp [henv] at h
          cases h
          refine ⟨fr, env', ?_, rfl, rfl, rfl, rfl, rfl⟩
          rfl

 theorem declareGlobalObject_success_fresh
    (s : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    ∃ s',
      s.declareGlobalObject x ty obj initialized = .ok s.nextLoc s' ∧
      s'.env.global = (Env.bindGlobal s.env x s.nextLoc).global ∧
      s'.env.locals = s.env.locals ∧
      s'.readCell s.nextLoc = some
        { ty := ty, object := obj, storage := .global, initialized := initialized, alive := true } ∧
      s'.funcs = s.funcs ∧
      s'.structs = s.structs ∧
      s'.nextLoc = s.nextLoc + 1 := by
  refine ⟨{ env := Env.bindGlobal s.env x s.nextLoc
          , store := Store.write s.store s.nextLoc
              { ty := ty, object := obj, storage := .global, initialized := initialized, alive := true }
          , funcs := s.funcs
          , structs := s.structs
          , nextLoc := s.nextLoc + 1 }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [declareGlobalObject_eq]
  · rfl
  · rfl
  · simp [State.readCell, Store.read_write_eq]
  · rfl
  · rfl
  · rfl

 theorem allocHeapObject_success_fresh
    (s : State) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    ∃ s',
      s.allocHeapObject ty obj initialized = .ok (.ptr s.nextLoc) s' ∧
      s'.env = s.env ∧
      s'.readCell s.nextLoc = some
        { ty := ty, object := obj, storage := .heap, initialized := initialized, alive := true } ∧
      s'.funcs = s.funcs ∧
      s'.structs = s.structs ∧
      s'.nextLoc = s.nextLoc + 1 := by
  refine ⟨{ env := s.env
          , store := Store.write s.store s.nextLoc
              { ty := ty, object := obj, storage := .heap, initialized := initialized, alive := true }
          , funcs := s.funcs
          , structs := s.structs
          , nextLoc := s.nextLoc + 1 }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [allocHeapObject_eq]
  · rfl
  · simp [State.readCell, Store.read_write_eq]
  · rfl
  · rfl
  · rfl

private theorem bindCurrentLocal?_cons_exact
    (global fr : Frame) (rest : List Frame) (x : Ident) (l : Loc) :
    Env.bindCurrentLocal?
      { global := global, locals := fr :: rest } x l
      =
      some { global := global, locals := (fr.bind x l) :: rest } := by
  simp [Env.bindCurrentLocal?]

private theorem ownCurrentLocal?_cons_exact
    (global fr : Frame) (rest : List Frame) (l : Loc) :
    Env.ownCurrentLocal?
      { global := global, locals := fr :: rest } l
      =
      some { global := global, locals := fr.own l :: rest } := by
  simp [Env.ownCurrentLocal?]

private theorem declareStackObject_cons_exact
    (global fr : Frame) (rest : List Frame)
    (store : Store) (funcs : _) (structs : _) (nextLoc : Loc)
    (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    State.declareStackObject
      { env := { global := global, locals := fr :: rest }
      , store := store
      , funcs := funcs
      , structs := structs
      , nextLoc := nextLoc } x ty obj initialized
    =
      .ok nextLoc
        { env :=
            { global := global
            , locals := ((fr.bind x nextLoc).own nextLoc) :: rest }
        , store :=
            Store.write store nextLoc
              { ty := ty
              , object := obj
              , storage := .stack
              , initialized := initialized
              , alive := true }
        , funcs := funcs
        , structs := structs
        , nextLoc := nextLoc + 1 } := by
  simp [declareStackObject_eq,
    State.bindCurrentLocal?, State.ownCurrentLocal?,
    bindCurrentLocal?_cons_exact, ownCurrentLocal?_cons_exact]



private theorem allocCell_env_eq
    (s : State) (c : Cell) :
    (s.allocCell c).snd.env = s.env := by
  simp [State.allocCell]

private theorem allocCell_funcs_eq
    (s : State) (c : Cell) :
    (s.allocCell c).snd.funcs = s.funcs := by
  simp [State.allocCell]

private theorem allocCell_structs_eq
    (s : State) (c : Cell) :
    (s.allocCell c).snd.structs = s.structs := by
  simp [State.allocCell]

private theorem declareStackObject_nil_ne_ok
    (global : Frame) (store : Store) (funcs : FuncTable) (structs : StructTable)
    (nextLoc : Loc)
    (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true)
    (l : Loc) (s' : State) :
    State.declareStackObject
      { env := { global := global, locals := [] }
      , store := store, funcs := funcs, structs := structs, nextLoc := nextLoc }
      x ty obj initialized
    ≠ EvalResult.ok l s' := by
  let s0 : State := ⟨⟨global, []⟩, store, funcs, structs, nextLoc⟩
  let cell : Cell :=
    { ty := ty, object := obj, storage := .stack, initialized := initialized, alive := true }
  change s0.declareStackObject x ty obj initialized ≠ EvalResult.ok l s'
  intro h
  have hbind :
      State.bindCurrentLocal? (s0.allocCell cell).snd x (s0.allocCell cell).fst = none := by
    simp [State.bindCurrentLocal?, Env.bindCurrentLocal?, allocCell_env_eq, s0, cell]
  simp [State.declareStackObject,  hbind, s0, cell] at h

theorem declareStackObject_success_contract
    (s s' : State) (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true)
    (l : Loc)
    (h : s.declareStackObject x ty obj initialized = .ok l s') :
    l = s.nextLoc ∧
    s'.readCell l = some
      { ty := ty, object := obj, storage := .stack, initialized := initialized, alive := true } ∧
    s'.funcs = s.funcs ∧
    s'.structs = s.structs ∧
    s'.nextLoc = s.nextLoc + 1 ∧
    ∃ fr rest,
      s.env.locals = fr :: rest ∧
      s'.env.global = s.env.global ∧
      s'.env.locals = ((fr.bind x l).own l) :: rest := by
  cases s with
  | mk env store funcs structs nextLoc =>
      cases env with
      | mk global locals =>
          cases locals with
          | nil =>
              exfalso
              exact declareStackObject_nil_ne_ok global store funcs structs nextLoc
               x ty obj initialized l s' h
          | cons fr rest =>
              rw [declareStackObject_cons_exact
                    global fr rest store funcs structs nextLoc
                    x ty obj initialized] at h
              cases h
              refine ⟨rfl, ?_, rfl, rfl, rfl, ?_⟩
              · simp [State.readCell, Store.read_write_eq]
              · exact ⟨fr, rest, rfl, rfl, rfl⟩

 theorem writeScalar_success_readback
    (s : State) (l : Loc) (v : RValue) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    ∃ s',
      s.writeScalar l v = .ok PUnit.unit s' ∧
      s'.readCell l = some (c.overwriteScalar v) ∧
      s'.env = s.env ∧
      s'.funcs = s.funcs ∧
      s'.structs = s.structs ∧
      s'.nextLoc = s.nextLoc := by
  refine ⟨{ s with store := Store.write s.store l (c.overwriteScalar v) }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact writeScalar_alive_eq s l v c hread halive
  · simp [State.readCell, Store.read_write_eq]
  · rfl
  · rfl
  · rfl
  · rfl

 theorem writeObject_success_readback
    (s : State) (l : Loc) (obj : Object) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    ∃ s',
      s.writeObject l obj = .ok PUnit.unit s' ∧
      s'.readCell l = some (c.overwriteObject obj) ∧
      s'.env = s.env ∧
      s'.funcs = s.funcs ∧
      s'.structs = s.structs ∧
      s'.nextLoc = s.nextLoc := by
  refine ⟨{ s with store := Store.write s.store l (c.overwriteObject obj) }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact writeObject_alive_eq s l obj c hread halive
  · simp [State.readCell, Store.read_write_eq]
  · rfl
  · rfl
  · rfl
  · rfl

end Contracts

-- ============================================================
-- §4. Current-WF preservation (light version)
-- ============================================================

section WFPreservation

theorem exitScope_success_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s s' : State) (hWF : s.WF)
    (hexit : s.exitScope = .ok PUnit.unit s') :
    s'.WF := by
  rcases hWF with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  rcases exitScope_success_store_eq s s' hexit with
    ⟨fr, env', henvExit, henv', hstore', hfuncs', hstructs', hnext'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have henv'' : env'.WF := Env.WF_exitScope_some henv fr env' henvExit
    simpa [henv'] using henv''
  · rw [hstore']
    exact Store.WF_killMany hstore fr.owned
  · rw [hfuncs']
    exact hfuncs
  · rw [hstructs']
    exact hstructs
  · rw [hnext']
    exact hnext

 theorem declareGlobalObject_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s : State) (hWF : s.WF)
    (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true) :
    ∃ l s', s.declareGlobalObject x ty obj initialized = .ok l s' ∧ s'.WF := by
  rcases hWF with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  refine ⟨s.nextLoc,
    { env := Env.bindGlobal s.env x s.nextLoc
    , store := Store.write s.store s.nextLoc
        { ty := ty, object := obj, storage := .global, initialized := initialized, alive := true }
    , funcs := s.funcs
    , structs := s.structs
    , nextLoc := s.nextLoc + 1 }, ?_, ?_⟩
  · simp [declareGlobalObject_eq]
  exact ⟨Env.WF_bindGlobal henv x s.nextLoc,
      Store.WF_write hstore s.nextLoc _,hfuncs,hstructs,by simp [nullLoc]⟩

 theorem allocHeapObject_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s : State) (hWF : s.WF)
    (ty : CppType) (obj : Object) (initialized : Bool := true) :
    ∃ s', s.allocHeapObject ty obj initialized = .ok (.ptr s.nextLoc) s' ∧ s'.WF := by
  rcases hWF with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  refine ⟨{ env := s.env
          , store := Store.write s.store s.nextLoc
              { ty := ty, object := obj, storage := .heap, initialized := initialized, alive := true }
          , funcs := s.funcs
          , structs := s.structs
          , nextLoc := s.nextLoc + 1 }, ?_, ?_⟩
  · simp [allocHeapObject_eq]
  · exact ⟨henv, Store.WF_write hstore s.nextLoc _, hfuncs, hstructs,by simp [nullLoc] ⟩

 theorem declareStackObject_success_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s s' : State) (hWF : s.WF)
    (x : Ident) (ty : CppType) (obj : Object) (initialized : Bool := true)
    (l : Loc)
    (hdecl : s.declareStackObject x ty obj initialized = .ok l s') :
    s'.WF := by
  rcases hWF with ⟨henv, hstore, hfuncs, hstructs, hnext⟩
  cases s with
  | mk env store funcs structs nextLoc =>
      cases env with
      | mk global locals =>
          cases locals with
          | nil =>
              simp [declareStackObject_eq, State.bindCurrentLocal?, Env.bindCurrentLocal?] at hdecl
                    | cons fr rest =>
              simp [declareStackObject_eq, State.bindCurrentLocal?, State.ownCurrentLocal?,
                Env.bindCurrentLocal?, Env.ownCurrentLocal?] at hdecl
              cases hdecl
              rcases henv with ⟨hg, hls⟩
              rcases hls with ⟨hfr, hrest⟩
              subst l
              subst s'
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨hg, ⟨Frame.WF_own (Frame.WF_bind hfr x nextLoc) nextLoc, hrest⟩⟩
              · exact Store.WF_write hstore nextLoc
                  { ty := ty, object := obj, storage := .stack, initialized := initialized, alive := true }
              · exact hfuncs
              · exact hstructs
              · simp [nullLoc]

 theorem writeScalar_success_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s : State) (hWF : s.WF) (l : Loc) (v : RValue) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    ∃ s', s.writeScalar l v = .ok PUnit.unit s' ∧ s'.WF := by
  refine ⟨{ s with store := Store.write s.store l (c.overwriteScalar v) }, ?_, ?_⟩
  · exact writeScalar_alive_eq s l v c hread halive
  · exact State.WF_writeCell hWF l _

 theorem writeObject_success_preserves_WF
    [DecidableEq Loc] [DecidableEq Ident]
    (s : State) (hWF : s.WF) (l : Loc) (obj : Object) (c : Cell)
    (hread : s.readCell l = some c) (halive : c.alive = true) :
    ∃ s', s.writeObject l obj = .ok PUnit.unit s' ∧ s'.WF := by
  refine ⟨{ s with store := Store.write s.store l (c.overwriteObject obj) }, ?_, ?_⟩
  · exact writeObject_alive_eq s l obj c hread halive
  · exact State.WF_writeCell hWF l _

end WFPreservation

end Cpp
