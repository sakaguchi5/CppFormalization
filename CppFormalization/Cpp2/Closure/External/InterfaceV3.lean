import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3
import CppFormalization.Cpp2.Closure.External.GlueV3
import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3

/-!
# Closure.External.InterfaceV3

Canonical Stage 2A V3 re-export.

Provided routes:
- low-level explicit target-indexed pieces route via `GlueV3`,
- higher-level integrated target-indexed route via `ReadyAssemblyV3`,
- canonical adapter from low-level glue to the integrated ready route.

Main redesign point:
- reflection chooses one package `(structural, profile, core)` together,
- glue proves adequacy only for that chosen profile,
- ready assembly carries explicit coherence back to the visible package side.
-/
