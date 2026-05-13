import CppFormalization.Cpp2.Typing.Expr
import CppFormalization.Cpp2.Typing.Stmt
import CppFormalization.Cpp2.Typing.ControlIndexed
import CppFormalization.Cpp2.Typing.TopFrameWitness
import CppFormalization.Cpp2.Typing.ControlEntryWitness
import CppFormalization.Cpp2.Typing.ControlProfile
import CppFormalization.Cpp2.Typing.ControlProfileLite

/-!
# CppFormalization.Cpp2.Typing.All

Exhaustive aggregate for this directory.

This file imports every Lean file directly under this directory, except itself,
and every immediate child directory through that child directory's `All.lean`.
-/
--依存関係
/-
Core
  ├─ Typing.Expr(Core.TypeEnv
  │              Core.Syntax)
  │    └─ Typing.Stmt
  │         └─ Typing.ControlIndexed(Core.Control)
  │              ├─ Typing.ControlEntryWitness
  │              ├─ Typing.ControlProfile
  │              └─ Typing.ControlProfileLite
  └─ Typing.TopFrameWitness(Core.TypeEnv)

Typing.Expr                : Core の型環境 + 構文から expression typing
Typing.Stmt                : expression typing の上に statement/block typing
Typing.ControlIndexed      : statement typing の上に control-indexed typing
Typing.TopFrameWitness     : type-env top frame witness helper
Typing.ControlEntryWitness : CI typing channel witness
Typing.ControlProfile      : CI typing summary/profile vocabulary
Typing.ControlProfileLite  : lite CI profile and coarse typing recovery
-/
