import CppFormalization.Cpp2.Core.RuntimeState

namespace Cpp

/-!
Low-level object-update core, independent of Closure/Foundation.

This file now carries only the raw definitions.  Projection and transport
facts for primitive state updates live in `Lemmas.RuntimeState`; projection and
transport facts for the object-core update live in `Lemmas.RuntimeObjectCore`.

The object-declaration update is split into:
- object payload update (`declareObjectStateCore`)
- cursor replacement (`setNext` / `declareObjectStateWithNext`)

so that allocator/cursor policy can stay separate from the payload semantics.
-/

/-- Replace only the cursor field. -/
def setNext (σ : State) (a : Nat) : State :=
  { σ with next := a }

/--
`declareObjectState` without post-state cursor policy.

The newly declared object still lives at the pre-state cursor `σ.next`.
What changes here are only:
- top binding
- heap cell at `σ.next`
- top-frame ownership/local recording

The next cursor is intentionally left unchanged.
-/
def declareObjectStateCore (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 := writeHeap σ1 a { ty := τ, value := ov, alive := true }
  recordLocal σ2 a

/--
Object declaration with externally supplied post-state cursor.

This is still deterministic as a function once the chosen cursor is given,
but it no longer hardcodes `next := σ.next + 1`.
-/
def declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) : State :=
  setNext (declareObjectStateCore σ τ x ov) aNext

end Cpp
