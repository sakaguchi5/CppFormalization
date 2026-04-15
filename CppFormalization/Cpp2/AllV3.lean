import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Closure.External.InterfaceV3
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosureV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3
import CppFormalization.Cpp2.Proof.All

/-!
# Cpp2.AllV3

Canonical aggregate for the V3 external assembly layer.

方針:
- 共通の closure / proof aggregate は `Closure.All` と `Proof.All` から読む。
- V3 固有の external assembly surface はこの file で追加する。
- Frontier は canonical aggregate には含めない。
-/
