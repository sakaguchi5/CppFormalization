import CppFormalization.Cpp2.Closure.Foundation.TypingCI

import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap

import CppFormalization.Cpp2.Closure.External.InterfaceV3
import CppFormalization.Cpp2.Closure.External.AdequacyKernelV3
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosureV3

import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3

/-!
# Cpp2.Closure.AllV3

Canonical aggregate for the V3 external assembly layer.

方針:

- V3 aggregate の canonical surface は Compat-based route とする。

- explicit glue route は low-level specialization として残す。

- legacy bridge は migration / quarantine 用の adapter として扱い、
  canonical public surface には含めない。

- toy inhabited instance もここで build 対象に含め、
  V3 API が abstract shell に留まらないことを確認する。

-/
