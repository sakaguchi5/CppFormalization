import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmap
import CppFormalization.Cpp2.Closure.External.InterfaceV3
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosureV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3

/-!
# Cpp2.Closure.AllV3

Canonical aggregate for the V3 external assembly layer.

方針:
- V3 aggregate は target-indexed explicit pieces route と
  integrated ready route の両方を公開面にする。
- V2 の露出した glue という利点は保ったまま、
  artifact applicability を表面に戻す。
- toy inhabited instance もここで build 対象に含め、
  V3 API が abstract shell に留まらないことを確認する。
-/
