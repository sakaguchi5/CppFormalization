import CppFormalization.Cpp2.Static.Safety.Assumptions

/-!
# CppFormalization.Cpp2.Static.Safety.All

Aggregate for static safety vocabulary.

`Static.Safety` may depend on Core, Typing, Semantics, and `Static.Pure`.
It must not depend on Closure, adequacy, preservation, or boundary assembly.
-/
--依存関係
/-
Core
  ├─ Semantics.Expr(Core.RuntimeState
  │                 Core.Syntax)
  ├─ Typing.Expr(Core.TypeEnv
  │              Core.Syntax)
  │    └─ Typing.Stmt
  ├─ Static.WellFormed(Core.Syntax)
  ├─ Static.ScopeDiscipline(Core.Syntax)
  ├─ Core.RuntimeState
  └─ Core.DeclRuntimeMatch

Static.Safety
  └─ Assumptions(Semantics.Expr
                 Typing.Stmt
                 Static.WellFormed
                 Static.ScopeDiscipline
                 Core.RuntimeState
                 Core.DeclRuntimeMatch)
-/
