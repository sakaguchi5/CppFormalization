import CppFormalization.Cpp2.Core.Types

-- Base vocabularies built directly on `Types`.
import CppFormalization.Cpp2.Core.Control
import CppFormalization.Cpp2.Core.Syntax
import CppFormalization.Cpp2.Core.TypeEnv
import CppFormalization.Cpp2.Core.RuntimeState

-- Pure syntax / environment / runtime observation vocabulary.
import CppFormalization.Cpp2.Core.SyntaxShape
import CppFormalization.Cpp2.Core.Fragment
import CppFormalization.Cpp2.Core.TypeEnvQuery
import CppFormalization.Cpp2.Core.RuntimeCell
import CppFormalization.Cpp2.Core.RuntimeQuery
import CppFormalization.Cpp2.Core.RuntimeFreshness
import CppFormalization.Cpp2.Core.DeclRuntimeMatch
import CppFormalization.Cpp2.Core.Outcome

-- Primitive runtime update operations and C++ declaration-state updates.
import CppFormalization.Cpp2.Core.RuntimeOps
import CppFormalization.Cpp2.Core.RuntimeDeclUpdate

-- Core theorem APIs sit above the definitions they describe.
import CppFormalization.Cpp2.Core.Facts.All

/-!
# CppFormalization.Cpp2.Core.All

Layered aggregate for the Core substrate.

This file is intentionally ordered by dependency and responsibility, not
alphabetically.
-/
--Core内の依存関係を図で示す
/-
Core.Types
  ├─ Core.Control
  ├─ Core.Syntax
  │    ├─ Core.SyntaxShape
  │    └─ Core.Fragment
  ├─ Core.TypeEnv
  │    └─ Core.TypeEnvQuery
  └─ Core.RuntimeState
       ├─ Core.RuntimeCell
       ├─ Core.RuntimeQuery
       ├─ Core.RuntimeFreshness
       ├─ Core.DeclRuntimeMatch
       ├─ Core.Outcome
       └─ Core.RuntimeOps
            └─ Core.RuntimeDeclUpdate

Core.Facts
  sits above the Core definitions and should not be imported before the
  definitions it states facts about.
-/
