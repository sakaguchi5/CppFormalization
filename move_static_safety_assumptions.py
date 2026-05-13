#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Create Static/Safety and move Static.Assumptions there.

Base repo expectation:
  sakaguchi5/CppFormalization around commit 89bae04714ea40b4aa3eadace16265c07f26c88c

This is the first Static/Safety refactoring step.

It moves:
  Cpp2/Static/Assumptions.lean
    -> Cpp2/Static/Safety/Assumptions.lean

and leaves:
  Cpp2/Static/Assumptions.lean

as a compatibility wrapper.  This keeps existing imports working while making
the intended layer explicit.

Why this step first?
  Closure.Foundation.Readiness currently depends on safety predicates such as
  ValidPlace / NoUninit* / NoInvalidRef* and on coarse IdealAssumptions-style
  vocabulary.  Before moving Readiness, the safety vocabulary needs a canonical
  Static/Safety home that does not point back to Closure.
"""

from __future__ import annotations

from pathlib import Path


ROOT_MARKERS = ("lakefile.lean", "lakefile.toml", "lean-toolchain")


def find_repo_root(start: Path) -> Path:
    cur = start.resolve()
    for p in (cur, *cur.parents):
        if any((p / marker).exists() for marker in ROOT_MARKERS) and (p / "CppFormalization").exists():
            return p
    raise SystemExit("Could not find repo root. Run this script from inside the CppFormalization repo.")


ROOT = find_repo_root(Path.cwd())
CPP2 = ROOT / "CppFormalization" / "Cpp2"

OLD = CPP2 / "Static" / "Assumptions.lean"
SAFETY_DIR = CPP2 / "Static" / "Safety"
NEW = SAFETY_DIR / "Assumptions.lean"
SAFETY_ALL = SAFETY_DIR / "All.lean"
STATIC_ALL = CPP2 / "Static" / "All.lean"


def read(path: Path) -> str:
    if not path.exists():
        raise SystemExit(f"Missing expected file: {path}")
    return path.read_text(encoding="utf-8")


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def all_lean_files() -> list[Path]:
    return sorted((ROOT / "CppFormalization").rglob("*.lean"))


# ---------------------------------------------------------------------------
# 1. Move Static.Assumptions content to Static.Safety.Assumptions.
# ---------------------------------------------------------------------------

old_text = read(OLD)
new_text = old_text.replace(
    "/-!\nSafety predicates and ideal boundary assumptions.\n-/",
    "/-!\n# CppFormalization.Cpp2.Static.Safety.Assumptions\n\n"
    "Safety predicates and ideal boundary assumptions.\n\n"
    "This file sits above Core, Typing, Semantics.Expr, and pure Static facts.\n"
    "It does not depend on Closure, adequacy, or preservation layers.\n"
    "-/",
)
write(NEW, new_text)

# Compatibility wrapper at the old path.
write(
    OLD,
    """import CppFormalization.Cpp2.Static.Safety.Assumptions

/-!
# CppFormalization.Cpp2.Static.Assumptions

Compatibility wrapper.

The safety predicates and ideal boundary assumptions now live in
`CppFormalization.Cpp2.Static.Safety.Assumptions`.
-/
""",
)


# ---------------------------------------------------------------------------
# 2. Create Static.Safety.All.
# ---------------------------------------------------------------------------

safety_all_text = """import CppFormalization.Cpp2.Static.Safety.Assumptions

/-!
# CppFormalization.Cpp2.Static.Safety.All

Aggregate for static safety vocabulary.

`Static.Safety` may depend on Core, Typing, Semantics, and `Static.Pure`.
It must not depend on Closure, adequacy, preservation, or boundary assembly.
-/
--依存関係
/-
Core
  ├─ Semantics.Expr(Core.RuntimeState
  │                 Core.Syntax)
  ├─ Typing.Expr(Core.TypeEnv
  │              Core.Syntax)
  │    └─ Typing.Stmt
  ├─ Static.WellFormed(Core.Syntax)
  ├─ Static.ScopeDiscipline(Core.Syntax)
  ├─ Core.RuntimeState
  └─ Core.DeclRuntimeMatch

Static.Safety
  └─ Assumptions(Semantics.Expr
                 Typing.Stmt
                 Static.WellFormed
                 Static.ScopeDiscipline
                 Core.RuntimeState
                 Core.DeclRuntimeMatch)
-/
"""
write(SAFETY_ALL, safety_all_text)


# ---------------------------------------------------------------------------
# 3. Update Static.All.
# ---------------------------------------------------------------------------

static_all = read(STATIC_ALL)
safety_import = "import CppFormalization.Cpp2.Static.Safety.All\n"
if safety_import not in static_all:
    pure_import = "import CppFormalization.Cpp2.Static.Pure.All\n"
    if pure_import in static_all:
        static_all = static_all.replace(pure_import, pure_import + safety_import)
    else:
        static_all = safety_import + static_all
    write(STATIC_ALL, static_all)


# ---------------------------------------------------------------------------
# 4. Rewrite direct imports where safe.
# ---------------------------------------------------------------------------

old_import = "import CppFormalization.Cpp2.Static.Assumptions"
new_import = "import CppFormalization.Cpp2.Static.Safety.Assumptions"

changed = []
for lean in all_lean_files():
    if lean == OLD:
        continue
    text = lean.read_text(encoding="utf-8")
    if old_import in text:
        text2 = text.replace(old_import, new_import)
        write(lean, text2)
        changed.append(lean.relative_to(ROOT))

print("Moved Static.Assumptions to Static.Safety.Assumptions.")
print("Left a compatibility wrapper at Static.Assumptions.")
print("Updated Static.Safety.All and Static.All.")
if changed:
    print("Rewrote imports in:")
    for p in changed:
        print(f"  {p}")
print("Next: run `lake build`.")
