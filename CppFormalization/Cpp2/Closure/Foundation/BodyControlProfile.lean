import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp.ClosureV2

/-!
# Closure.Foundation.BodyControlProfile

四層分離の第2層: control-sensitive static profile.

役割:
- statement / opened block body の exit channel 要約を保持する。
- `Δ` は mere existence ではなく payload として保持する。

注意:
- 既存 `Cpp.BodyExitKind` / `StmtBodySummary` / `BlockBodySummary` との衝突を避けるため、
  移行中は `Cpp.ClosureV2` namespace に隔離する。
-/

inductive BodyExitKind where
  | normal
  | returned
  deriving DecidableEq, Repr

structure StmtBodySummary (Γ : TypeEnv) (st : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}

structure BlockBodySummary (Γ : TypeEnv) (ss : StmtBlock) : Type where
  normalOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ}
  returnOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ}

structure BodyControlProfile (Γ : TypeEnv) (st : CppStmt) : Type where
  summary : StmtBodySummary Γ st

structure BlockBodyControlProfile (Γ : TypeEnv) (ss : StmtBlock) : Type where
  summary : BlockBodySummary Γ ss

end Cpp.ClosureV2
