import CppFormalization.Cpp2.Semantics.Expr
import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Semantics.Facts.All

/-!
# CppFormalization.Cpp2.Semantics.All

Exhaustive aggregate for this directory.

This file imports every Lean file directly under this directory, except itself,
and every immediate child directory through that child directory's `All.lean`.
-/
--依存関係
/-
Core
  └─ Semantics.Expr(Core.RuntimeState
                    Core.Syntax)
       └─ Semantics.Stmt(Core.RuntimeDeclUpdate
                         Core.RuntimeFreshness
                         Core.Control)
            └─ Semantics.Divergence
-/
