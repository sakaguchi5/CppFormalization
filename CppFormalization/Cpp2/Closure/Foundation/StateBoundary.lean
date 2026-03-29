import CppFormalization.Cpp2.Static.Assumptions

namespace Cpp

/-!
# Closure.Foundation.StateBoundary

Closure theorem へ向かうための「状態境界」と「開始準備条件」の層。

意図:
- 旧 `IdealAssumptions` を、そのまま closure の前提にしない。
- runtime invariant と statement-local safety を分ける。
- 既存 Core の theorem を壊さず、その上に乗る新しい境界語彙を用意する。
-/

axiom scopesCompatible : TypeEnv → State → Prop
axiom framewiseDeclBindingCompatible : TypeEnv → State → Prop
axiom objectBindingsLiveTypedOwned : TypeEnv → State → Prop
axiom refBindingsLiveTyped : TypeEnv → State → Prop
axiom frameLocalsExact : TypeEnv → State → Prop
axiom ownedAddressesDisjoint : State → Prop
axiom heapInitializedValuesTyped : State → Prop
axiom nextIsFreshForOwnedHeap : State → Prop

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
定義の中に `∃ a, BigStepPlace σ p a` を直接埋め込まない。
-/
axiom PlaceReady : TypeEnv → State → PlaceExpr → CppType → Prop

/--
`ExprReady Γ σ e τ` は、`e` が現在の状態で安全に評価できる `τ`-expr であること。
こちらも進行定理を空虚にしないため、評価可能性そのものは定義に埋め込まない。
-/
axiom ExprReady : TypeEnv → State → ValExpr → CppType → Prop

/--
statement / block 開始時の安全準備条件。
`ScopedTypedState` が状態側、`StmtReady` / `BlockReady` が文局所側を受け持つ。
-/
axiom StmtReady : TypeEnv → State → CppStmt → Prop
axiom BlockReady : TypeEnv → State → StmtBlock → Prop

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

/--
旧 `IdealAssumptions` から新しい `BodyReady` へ移るための橋。
これは最終的には theorem にすべきだが、最初は interface として切り出す。
-/
axiom bodyReady_of_idealAssumptions
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st →
    BodyReady Γ σ st

end Cpp
