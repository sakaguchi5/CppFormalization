import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary

namespace Cpp.ClosureV2

/-!
# Closure.Foundation.BodyAdequacyCI

四層分離の第4層: profile と actual big-step を結ぶ adequacy.

役割:
- `summary` が実際の実行導出に対して正しい payload を返すことを述べる。
- structural / dynamic から独立させ、closure driver 側の責務を分離する。
-/

structure BodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepStmt σ st .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        P.summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepStmt σ st (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        P.summary.returnOut = some out

structure BlockBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ},
        P.summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ},
        P.summary.returnOut = some out

end Cpp.ClosureV2
