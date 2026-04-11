import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.InterfaceV3
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosureV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3

/-!
# Cpp2.Closure.AllV3

Canonical aggregate for the V3 external assembly layer.

方針:
- V3 aggregate の honest canonical route は
  `Compat + CanonicalAdequacyContractsV3` から
  `ReflectiveStdClosureV3.*_ofContracts` へ入る流れである。
- 旧 `Compat -> canonicalGlueV3` ルートは、generic kernel 由来の
  provisional shortcut として残す。
- explicit glue route は low-level specialization として残す。
- toy inhabited instance もここで build 対象に含め、V3 API が abstract shell
  に留まらないことを確認する。
-/
