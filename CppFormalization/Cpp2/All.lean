import CppFormalization.Cpp2.Closure.All
import CppFormalization.Cpp2.Proof.All

/-!
# Cpp2.All

Canonical aggregate for the current Cpp2 surface.

方針:
- `Closure.All` を通して closure mainline と internal transport aggregate を拾う。
- `Proof.All` を通して control / preservation / determinism aggregate を拾う。
- Frontier は canonical aggregate には含めない。
-/
