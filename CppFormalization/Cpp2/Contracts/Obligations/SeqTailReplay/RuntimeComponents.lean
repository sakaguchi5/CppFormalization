import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Basic

namespace Cpp

/-!
# Seq tail replay: runtime component package
-/

/--
Read-set non-clobbering component for the selected tail route.

Compared with the old `witness : True` placeholder, this component now records
two constructor-oriented slots:

* `stmtShape` follows the constructors of `StmtReadyConcrete`;
* `ordinaryReads` is the future hook for ordinary expression/place replay.

The C++-dangerous deref/load cases stay in their own components below.
-/
structure SeqTailReadSetNonClobberAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  stmtShape : SeqTailStmtConstructorReplayAtRouteCI route
  ordinaryReads : SeqTailOrdinaryReadReplayAtRouteCI route

namespace SeqTailReadSetNonClobberAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailReadSetNonClobberAtRouteCI route :=
  { stmtShape := SeqTailStmtConstructorReplayAtRouteCI.trivial
    ordinaryReads := SeqTailOrdinaryReadReplayAtRouteCI.trivial }

end SeqTailReadSetNonClobberAtRouteCI

/--
Pointer/deref stability component for the selected tail route.

This is now a named wrapper around the future dereference replay slots, rather
than a bare placeholder.
-/
structure SeqTailPointerDerefStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  derefPointer : SeqTailDerefPointerReplayAtRouteCI route

namespace SeqTailPointerDerefStabilityAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailPointerDerefStabilityAtRouteCI route :=
  { derefPointer := SeqTailDerefPointerReplayAtRouteCI.trivial }

end SeqTailPointerDerefStabilityAtRouteCI

/--
Load readability preservation component for the selected tail route.

This is now a named wrapper around the future load-readability replay slots,
rather than a bare placeholder.
-/
structure SeqTailLoadReadabilityPreservationAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  loadReadability : SeqTailLoadReplayAtRouteCI route

namespace SeqTailLoadReadabilityPreservationAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailLoadReadabilityPreservationAtRouteCI route :=
  { loadReadability := SeqTailLoadReplayAtRouteCI.trivial }

end SeqTailLoadReadabilityPreservationAtRouteCI

/--
Runtime replay component of the tail stability contract.

The three named subcomponents are the C++-meaningful future split points.  At
this stage, `tailReady` is still the coarse runtime fact, but it is no longer
mixed with post-state preservation or tail static/profile adequacy.
-/
structure SeqTailRuntimeReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route
  tailReady : StmtReadyConcrete route.Θ σ1 t

namespace SeqTailRuntimeReplayAtRouteCI

/-- Compatibility constructor from the still-coarse tail readiness fact. -/
def ofTailReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (hready : StmtReadyConcrete route.Θ σ1 t) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := SeqTailReadSetNonClobberAtRouteCI.trivial
    derefPointer := SeqTailPointerDerefStabilityAtRouteCI.trivial
    loadReadability := SeqTailLoadReadabilityPreservationAtRouteCI.trivial
    tailReady := hready }

end SeqTailRuntimeReplayAtRouteCI

/--
Route-local stability contract for the tail of `s; t`.


/--
Runtime replay components for the selected tail route.

This is the next refinement below `SeqTailRuntimeReplayAtRouteCI`: the C++
meaningful parts are named separately, and the remaining coarse step is only the
materialization theorem/obligation that turns those components into ordinary
`StmtReadyConcrete`.
-/
-/
structure SeqTailRuntimeReplayComponentsAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route

end Cpp
