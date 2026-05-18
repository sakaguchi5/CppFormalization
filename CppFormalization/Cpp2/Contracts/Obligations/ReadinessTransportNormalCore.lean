import CppFormalization.Cpp2.Contracts.Obligations.ReadinessTransportNormal

namespace Cpp

/-!
# Contracts.Obligations.ReadinessTransportNormalCore

`Contracts.Obligations.ReadinessTransportNormal` で固定した transport context / goal aliases の上に、
将来の mutual ready-transport theorem family を一箇所へ束ねる core file。

この段階ではまだ theorem-backed 実装は入れない。

注意:
- この unrestricted core は最終的な theorem target ではなく、旧 general
  readiness-transport debt の互換 surface である。
- 今後の本線は `ReadinessTransportNormalRefined.lean` にあるように、
  env-preserving / env-extending-old / fresh-name introduction / read 条件へ
  分解して theorem-backed 化する。
- 特に env-extending head では fresh name は transport ではなく post-state
  binding から introduce する対象である。

代わりに、place / expr / stmt / block の4本の future core goals を
一つの bundled kernel にまとめる。

重要:
- これは「axiom を増やす」ためのファイルではない。
  既存の general readiness-transport debt を、将来 theorem に差し替えるための
  single choke point に集約するための file である。
- 以前この file に同居していた legacy exact seq/block tail-ready kernels は、
  `ReadinessTransportNormalExactTail.lean` へ分離した。
  これにより、ordinary readiness transport family と exact tail-ready debt を
  別々に縮小できる。
-/


/- =========================================================
   1. bundled future kernel surface
   ========================================================= -/

structure ReadinessTransportNormalCore : Type where
  placeTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      PlaceReadyTransportGoal Γ Δ σ σ' head

  exprTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ExprReadyTransportGoal Γ Δ σ σ' head

  stmtTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      StmtReadyTransportGoal Γ Δ σ σ' head

  blockTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      BlockReadyTransportGoal Γ Δ σ σ' head


/- =========================================================
   2. current bundled kernel
   ========================================================= -/

axiom readinessTransportNormalCore : ReadinessTransportNormalCore


/- =========================================================
   3. thin projection theorems
   ========================================================= -/

theorem place_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    PlaceReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.placeTransport

theorem expr_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ExprReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.exprTransport

theorem stmt_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    StmtReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.stmtTransport

theorem block_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    BlockReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.blockTransport
end Cpp
