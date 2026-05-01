import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ReflectionFragmentV3
import CppFormalization.Cpp2.Closure.External.GlueV3
import CppFormalization.Cpp2.Closure.External.AssembleV3
import CppFormalization.Cpp2.Closure.External.CoherenceV3
import CppFormalization.Cpp2.Closure.External.TransportV3
import CppFormalization.Cpp2.Closure.External.TransportPropsV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3
import CppFormalization.Cpp2.Closure.External.CanonicityV3
import CppFormalization.Cpp2.Closure.External.ReadyAssemblyV3
import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.BuilderV3
import CppFormalization.Cpp2.Closure.External.SplitBuilderV3
import CppFormalization.Cpp2.Closure.External.ToyBuilderV3
import CppFormalization.Cpp2.Closure.External.ToySplitBuilderV3
import CppFormalization.Cpp2.Closure.External.LegacyBuilderV3
import CppFormalization.Cpp2.Closure.External.AlignmentV3

/-!
# Closure.External.InterfaceV3

Canonical Stage 2A/2B/2C/4/5/6/7/8 V3 re-export.

Provided routes:
- low-level explicit target-indexed pieces route via `GlueV3`,
- higher-level integrated target-indexed route via `ReadyAssemblyV3`,
- canonical adapter from low-level glue to the integrated ready route,
- certificate-family builder route via `BuilderV3`,
- split-artifact preparatory builder route via `SplitBuilderV3`,
- first concrete builder consumer via `ToyBuilderV3`,
- first concrete split-builder consumer via `ToySplitBuilderV3`,
- legacy non-toy lift into the same V3 world via `LegacyBuilderV3`,
- Stage 6 alignment lemmas showing that the builder-generated canonical routes
  land on the same official quotient as the earlier hand-written toy routes and
  the earlier direct legacy bridge.

Main redesign point:
- reflection chooses one package `(structural, static, core)` together,
- glue proves adequacy only for the profile projected from that chosen static package,
- ready assembly carries explicit coherence back to the observable package side.

Stage 2B comparison vocabulary:
- `ObservablePiecesV3` is the official package-level carrier,
- `PackageCoherentV3` is the strong observable-package comparison notion,
- `BoundaryCoherentV3` is the official quotient used by closure theorems,
- `VisiblePiecesV3` is deliberately not part of the V3 public vocabulary.

Stage 2C family canonicity vocabulary:
- `RuntimePackageUniqueV3` says runtime artifacts are target-canonical,
- `ReflectionPackageUniqueV3` says reflection artifacts are target-canonical,
- `canonicalObservablePiecesV3_wellDefined` records that observable package choice
  no longer depends on which supporting artifact was used.
-/
