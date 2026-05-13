import CppFormalization.Cpp2.Typing.Expr
import CppFormalization.Cpp2.Typing.Stmt
import CppFormalization.Cpp2.Typing.ControlIndexed

/-!
# CppFormalization.Cpp2.Typing.All

Exhaustive aggregate for this directory.

This file imports every Lean file directly under this directory, except itself,
and every immediate child directory through that child directory's `All.lean`.
-/
--依存関係
/-
Core
  └─ Typing.Expr(Core.TypeEnv
                 Core.Syntax)
       └─ Typing.Stmt
            └─ Typing.ControlIndexed(Core.Control)

Typing.Expr          : Core の型環境 + 構文から expression typing
Typing.Stmt          : expression typing の上に statement/block typing
Typing.ControlIndexed: statement typing の上に control-indexed typing

-/
