import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyAdequacyCI

四層分離の第4層。

ここでは control profile が actual big-step exits に対して adequate であることを述べる。
summary 自体は state-free だが、その adequacy は state / execution に依存する。
したがって profile と adequacy は別層である。
-/

/-- Adequacy of a statement control profile against actual statement execution. -/
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

/-- Adequacy of an opened block-body profile against actual block execution. -/
structure BlockBodyAdequacyCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ},
        P.summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv //
        HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ},
        P.summary.returnOut = some out

end Cpp
