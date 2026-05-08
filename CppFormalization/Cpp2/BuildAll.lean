import CppFormalization.Cpp2.All

/-!
# Cpp2.BuildAll

`lake build` で Cpp2 の全 Lean module を拾うための build 用 aggregate.

Policy:
- `Cpp2.All` is the single Cpp2-wide aggregate.
- Directory-level `All.lean` files recursively import the modules below their
  directory.
- No Cpp2 directory is intentionally excluded from build coverage.
-/
