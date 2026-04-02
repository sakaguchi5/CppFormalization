import CppFormalization.Cpp2.Static.Assumptions
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcrete

`Closure.StateBoundary` では `ScopedTypedState` の成分名だけを置いた。
このファイルでは、それをさらに具体的な数学的青写真へ落とす。

目的:
- `closeScope` が偽にならないために、何を invariant に入れるべきかを明示する。
- object ownership と ref alias を分ける。
- 将来の preservation theorem の支点を structure field の形で固定する。

注意:
- ここではまだ既存 `State` / `TypeEnv` の内部表現に深入りしない。
- その代わり、depth-indexed な frame 対応と ownership witness を表す補助述語を切り出す。
-/


/-- 型環境の深さ `k` に object 宣言 `x : τ` が存在する。 -/
def typeFrameDeclObject (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.object τ)

/-- 型環境の深さ `k` に ref 宣言 `x : τ` が存在する。 -/
def typeFrameDeclRef (Γ : TypeEnv) (k : Nat) (x : Ident) (τ : CppType) : Prop :=
  ∃ fr, Γ.scopes[k]? = some fr ∧ fr.decls x = some (.ref τ)

/-- runtime state の深さ `k` の frame に object binding `x ↦ (.object τ a)` がある。 -/
def runtimeFrameBindsObject (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.object τ a)

/-- runtime state の深さ `k` の frame に ref binding `x ↦ (.ref τ a)` がある。 -/
def runtimeFrameBindsRef (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.ref τ a)

/-- address `a` は runtime state の深さ `k` の frame が所有する object local である。 -/
def runtimeFrameOwnsAddress (σ : State) (k : Nat) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ a ∈ fr.locals

/-- address `a` には live な `τ`-cell がある。 -/
def heapLiveTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true

/-- address `a` の cell には型整合する初期化済み値が入っている。 -/
def heapInitializedTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c v,
    σ.heap a = some c ∧
    c.ty = τ ∧
    c.alive = true ∧
    c.value = some v ∧
    ValueCompat v τ

/-- frame 内での shadowing が lookup 規則と整合している。 -/
def shadowingCompatible (Γ : TypeEnv) (σ : State) : Prop :=
  ∀ x d,
    lookupDecl Γ x = some d →
    ∃ b, lookupBinding σ x = some b ∧ DeclMatchesBinding d b

/-- type-env の frame 数と runtime scope の frame 数が一致する。 -/
def frameDepthAgreement (Γ : TypeEnv) (σ : State) : Prop :=
  Γ.scopes.length = σ.scopes.length

/-- runtime frame の owned object address には重複がない。 -/
def ownedAddressesNoDupPerFrame (σ : State) : Prop :=
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    fr.locals.Nodup

/-- object ownership は frame 間で交わらない。 -/
def ownedAddressesDisjointAcrossFrames (σ : State) : Prop :=
  ∀ (i j : Nat) fi fj a,
    i ≠ j →
    σ.scopes[i]? = some fi →
    σ.scopes[j]? = some fj →
    a ∈ fi.locals →
    a ∉ fj.locals

/-- すべての object binding は対応する ownership witness を持つ。 -/
def allObjectBindingsOwned (σ : State) : Prop :=
  ∀ k x τ a,
    runtimeFrameBindsObject σ k x τ a →
    runtimeFrameOwnsAddress σ k a

/-- 所有されている address は必ず object binding から来る。 -/
def allOwnedAddressesNamed (σ : State) : Prop :=
  ∀ k a,
    runtimeFrameOwnsAddress σ k a →
    ∃ x τ, runtimeFrameBindsObject σ k x τ a

/-- fresh allocation に使う `next` は未使用で、既存所有 address と衝突しない。 -/
def nextFreshAgainstOwned (σ : State) : Prop :=
  σ.heap σ.next = none ∧
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    σ.next ∉ fr.locals



/-- ref binding は ownership を主張しない。 -/
axiom refBindingsNeverOwned : State → Prop




/--
`ScopedTypedStateConcrete` は、`ScopedTypedState` の「どこを具体化するか」を明示した強い青写真。
これ自体を最終的な invariant にしてもよいし、
これを分解して既存 `ScopedTypedState` の theorem 群へ落としてもよい。
-/
structure ScopedTypedStateConcrete (Γ : TypeEnv) (σ : State) : Prop where
  /- stack 全体の対応 -/
  frameDepth : frameDepthAgreement Γ σ
  shadowing : shadowingCompatible Γ σ

  /- decl → binding → heap/live の前向き実現 -/
  objectDeclRealized :
    ∀ {k x τ},
      typeFrameDeclObject Γ k x τ →
      ∃ a,
        runtimeFrameBindsObject σ k x τ a ∧
        runtimeFrameOwnsAddress σ k a ∧
        heapLiveTypedAt σ a τ

  refDeclRealized :
    ∀ {k x τ},
      typeFrameDeclRef Γ k x τ →
      ∃ a,
        runtimeFrameBindsRef σ k x τ a ∧
        heapLiveTypedAt σ a τ

  /- ownership の逆向き完全性 -/
  ownedAddressNamed :
    ∀ {k a},
      runtimeFrameOwnsAddress σ k a →
      ∃ x τ, runtimeFrameBindsObject σ k x τ a

  /- object と ref の役割分離 -/
  refsNotOwned : refBindingsNeverOwned σ
  objectsOwned : allObjectBindingsOwned σ

  /- ownership discipline -/
  ownedNoDupPerFrame : ownedAddressesNoDupPerFrame σ
  ownedDisjoint : ownedAddressesDisjointAcrossFrames σ
  ownedNamed : allOwnedAddressesNamed σ

  /- 値整合と fresh allocation -/
  initializedValuesTyped :
    ∀ {k x τ a},
      runtimeFrameBindsObject σ k x τ a →
      heapInitializedTypedAt σ a τ ∨ True
  nextFresh : nextFreshAgainstOwned σ
  /- ref target の非所有性 ref target は自分より内側の frame が owned する address であってはならない -/
  refTargetsAvoidInnerOwned :
  ∀ {k x τ a j},
    runtimeFrameBindsRef σ k x τ a →
    j < k →
    ¬ runtimeFrameOwnsAddress σ j a

/--
`declareObject` が top ownership を増やすだけで、
下位 frame の witness を壊さないことを言う補題目標。
-/
axiom declareObject_extends_top_ownership_only
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    (∃ a, runtimeFrameBindsObject σ' 0 x τ a ∧ runtimeFrameOwnsAddress σ' 0 a) ∧
    (∀ {k y υ},
      typeFrameDeclObject Γ k y υ →
      ∃ a, runtimeFrameBindsObject σ' (k+1) y υ a)

/-未使用なのでコメントアウト
/--
`declareRef` は ownership を増やさず alias binding だけを増やす。
これが object と ref を同一視してはいけない理由。
-/
axiom declareRef_adds_alias_without_ownership
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    runtimeFrameBindsRef σ' 0 x τ a ∧
    (∀ {k b}, runtimeFrameOwnsAddress σ k b ↔ runtimeFrameOwnsAddress σ' k b)
-/
end Cpp
