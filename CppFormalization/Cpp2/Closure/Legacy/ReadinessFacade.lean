import CppFormalization.Cpp2.Closure.Legacy.RuntimeStateBoundary

namespace Cpp

/-!
# Closure.Legacy.ReadinessFacade

旧 `StateBoundary.lean` にあった coarse readiness / body facade を切り出した legacy 層。

位置づけ:
- 四層 core の一部ではない。
- old abstract roadmap / external facade 用の互換語彙である。
- `StateBoundary.lean` 自体は以後このファイルを再 export する薄い wrapper に降格する。
-/

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

end Cpp
