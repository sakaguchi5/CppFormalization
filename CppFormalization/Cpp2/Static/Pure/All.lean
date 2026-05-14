import CppFormalization.Cpp2.Static.Pure.WellFormedFromTyping
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundaryLite

/-!
# CppFormalization.Cpp2.Static.Pure.All

Aggregate for pure static facts.

These files may depend on Core, Typing, and other pure Static modules, but they
must not depend on runtime state, Semantics, readiness, adequacy, or Closure.
-/
--依存関係
/-
Core
  ├─ Static.WellFormed(Core.Syntax)
  ├─ Static.ScopeDiscipline(Core.Syntax)
  └─ Typing.Expr(Core.TypeEnv
                 Core.Syntax)
       └─ Typing.Stmt

Static.Pure
  ├─ WellFormedFromTyping(Static.WellFormed
  │                       Typing.Stmt)
  ├─ BodyStructuralBoundary(Static.WellFormed
  │                         Static.ScopeDiscipline
  │                         Core.TypeEnv)
  └─ BodyStructuralBoundaryLite(Static.WellFormed
                               Static.ScopeDiscipline)
-/
