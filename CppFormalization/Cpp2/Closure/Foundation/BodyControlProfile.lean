import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyControlProfile

四層分離の第2層。

ここでは statement / block の control-sensitive summary だけを持つ。
これは well-formedness でも readiness でもなく、
CI typing payload を伴う static profile である。
-/

/-- function-body top level で観測したい出口 channel. -/
inductive BodyExitKind where
  | normal
  | returned
  deriving DecidableEq, Repr

/--
statement 用の internal control summary.
`Δ` は mere existence ではなく channel payload の一部として保持する。
-/
structure StmtBodySummary (Γ : TypeEnv) (st : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}

/--
opened block body 用の internal control summary.
block-body は `pushTypeScope Γ` 下で見る。
-/
structure BlockBodySummary (Γ : TypeEnv) (ss : StmtBlock) : Type where
  normalOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ}
  returnOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ}

/-- State-free control profile for a statement body. -/
structure BodyControlProfile (Γ : TypeEnv) (st : CppStmt) : Type where
  summary : StmtBodySummary Γ st

/-- State-free control profile for an opened block body. -/
structure BlockBodyControlProfile (Γ : TypeEnv) (ss : StmtBlock) : Type where
  summary : BlockBodySummary Γ ss

end Cpp
