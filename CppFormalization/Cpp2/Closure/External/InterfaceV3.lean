import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3
import CppFormalization.Cpp2.Closure.External.GlueV3
import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.External.CoherenceV3
import CppFormalization.Cpp2.Closure.External.TransportV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3
import CppFormalization.Cpp2.Closure.External.CanonicityV3
import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.BuilderV3
import CppFormalization.Cpp2.Closure.External.LegacyBridgeV3
import CppFormalization.Cpp2.Closure.External.LegacyBuilderV3

/-!
# Closure.External.InterfaceV3

Canonical Stage 2A/2B/2C/Stage 4/Stage 5 V3 re-export.

Provided routes:
- low-level explicit target-indexed pieces route via `GlueV3`,
- higher-level integrated target-indexed route via `ReadyAssemblyV3`,
- canonical adapter from low-level glue to the integrated ready route,
- builder-generated families via `BuilderV3`,
- and the first non-toy legacy-family lift via `LegacyBuilderV3`.

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
- `canonicalVisiblePiecesV3_wellDefined` records that visible package choice no
  longer depends on which supporting artifact was used.

Stage 3.5 refactoring support vocabulary:
- `TransportV3` isolates profile-index transport / cast lemmas,
- `AssembleLemmasV3` isolates generic low-level assembly projections.

Stage 4/5 extension points:
- `BuilderV3` packages ready-certificate families into the V3 interfaces,
- `LegacyBuilderV3` lifts the old assumption-style external surface as the
  first non-toy builder-generated family.
-/
