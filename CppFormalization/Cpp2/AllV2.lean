import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Closure.External.InterfaceV2
import CppFormalization.Cpp2.Closure.External.ReflectiveStdClosureV2
import CppFormalization.Cpp2.Proof.All

/-!
# Cpp2.AllV2

Canonical aggregate for the explicit V2 external assembly layer.

方針:
- 共通の closure / proof aggregate は `Closure.All` と `Proof.All` から読む。
- V2 固有の external assembly surface はこの file で追加する。
- Frontier は canonical aggregate には含めない。
-/
