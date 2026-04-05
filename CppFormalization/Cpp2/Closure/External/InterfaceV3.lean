import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3
import CppFormalization.Cpp2.Closure.External.GlueV3
import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.External.CoherenceV3
import CppFormalization.Cpp2.Closure.External.CanonicityV3
import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3

/-!
# Closure.External.InterfaceV3

Canonical Stage 2A/2B/2C V3 re-export.

Provided routes:
- low-level explicit target-indexed pieces route via `GlueV3`,
- higher-level integrated target-indexed route via `ReadyAssemblyV3`,
- canonical adapter from low-level glue to the integrated ready route.

Main redesign point:
- reflection chooses one package `(structural, profile, core)` together,
- glue proves adequacy only for that chosen profile,
- ready assembly carries explicit coherence back to the visible package side.

Stage 2B comparison vocabulary:
- `PackageCoherentV3` is the strong visible-package comparison notion,
- `BoundaryCoherentV3` is the official quotient used by closure theorems.

Stage 2C family canonicity vocabulary:
- `RuntimePackageUniqueV3` says runtime artifacts are target-canonical,
- `ReflectionPackageUniqueV3` says reflection artifacts are target-canonical,
- `canonicalVisiblePiecesV3_wellDefined` records that visible package choice
  no longer depends on which supporting artifact was used.
-/
