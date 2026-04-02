import CppFormalization.Cpp2.Closure.Legacy.RuntimeStateBoundary
import CppFormalization.Cpp2.Closure.Legacy.ReadinessFacade
import CppFormalization.Cpp2.Closure.Legacy.InternalClosureRoadmapLegacy
import CppFormalization.Cpp2.Closure.Legacy.InterfaceLegacy
import CppFormalization.Cpp2.Closure.Legacy.ReflectiveStdClosureLegacy

/-!
# Cpp2.Closure.Legacy.All

Legacy aggregate for the pre-mainline-switch closure surfaces.

方針:
- old coarse `BodyReady` / `StmtReady` façade と、それに基づく old roadmap /
  external interface / external closure theorem を一か所に集約する。
- default `Closure.All` はこれを re-export しない。
-/
