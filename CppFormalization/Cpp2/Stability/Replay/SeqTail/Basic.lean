import CppFormalization.Cpp2.Route.ContinuationRoute.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI

namespace Cpp

/-!
# Seq tail replay: basic route-local contract skeleton
-/

/-!
# Seq tail replay / stability obligations

These are not closure shells: they are the conditions saying why the selected route can
enter the tail in the post-state.

Several components are still coarse placeholders.  The point of this move is to
make them visible as contract obligations, not as hidden closure internals.
-/

/--
Post-state component of the tail stability contract.

This is preservation-shaped: after the selected left-normal route, the route's
post-environment `route.Θ` and actual post-state `σ1` still agree concretely.
Long term, this component should be theorem-backed by normal preservation rather
than treated as a program contract.
-/
structure SeqTailPostStateAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  postState : ScopedTypedStateConcrete route.Θ σ1

/--
Name/scope/static component of the tail stability contract.

This is intentionally separated from runtime readiness.  The selected route
already determines `route.Θ`, and the tail static package lives exactly at that
environment.  This records the future split point for name-resolution and scope
stability.
-/
structure SeqTailNameScopeStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  typed0 : WellTypedFrom route.Θ t

/- =========================================================
   Constructor-aligned runtime replay skeleton
   ========================================================= -/

/--
Statement-constructor replay slots for the selected tail route.

This is intentionally still a lightweight contract skeleton: each field is a
slot corresponding to a `StmtReadyConcrete` constructor.  Later materialization
theorems can replace the `True` payloads by the exact constructor inputs
(`HasValueType`, `ExprReadyConcrete`, `PlaceReadyConcrete`, branch readiness,
and so on) without changing the route-level API.
-/
structure SeqTailStmtConstructorReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  skip :
    t = .skip → True
  exprStmt :
    ∀ {e : ValExpr}, t = .exprStmt e → True
  assign :
    ∀ {p : PlaceExpr} {e : ValExpr}, t = .assign p e → True
  declareObjNone :
    ∀ {τ : CppType} {x : Ident}, t = .declareObj τ x none → True
  declareObjSome :
    ∀ {τ : CppType} {x : Ident} {e : ValExpr},
      t = .declareObj τ x (some e) → True
  declareRef :
    ∀ {τ : CppType} {x : Ident} {p : PlaceExpr},
      t = .declareRef τ x p → True
  seq :
    ∀ {u v : CppStmt}, t = .seq u v → True
  ite :
    ∀ {c : ValExpr} {u v : CppStmt}, t = .ite c u v → True
  whileStmt :
    ∀ {c : ValExpr} {body : CppStmt}, t = .whileStmt c body → True
  block :
    ∀ {ss : StmtBlock}, t = .block ss → True
  breakStmt :
    t = .breakStmt → True
  continueStmt :
    t = .continueStmt → True
  returnNone :
    t = .returnStmt none → True
  returnSome :
    ∀ {e : ValExpr}, t = .returnStmt (some e) → True

namespace SeqTailStmtConstructorReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths that already have tail-ready. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailStmtConstructorReplayAtRouteCI route :=
  { skip := by intro _; trivial
    exprStmt := by intro e _; trivial
    assign := by intro p e _; trivial
    declareObjNone := by intro τ x _; trivial
    declareObjSome := by intro τ x e _; trivial
    declareRef := by intro τ x p _; trivial
    seq := by intro u v _; trivial
    ite := by intro c u v _; trivial
    whileStmt := by intro c body _; trivial
    block := by intro ss _; trivial
    breakStmt := by intro _; trivial
    continueStmt := by intro _; trivial
    returnNone := by intro _; trivial
    returnSome := by intro e _; trivial }

end SeqTailStmtConstructorReplayAtRouteCI

/-- Placeholder for replaying an ordinary value expression used by the selected tail. -/
def SeqTailValueUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_e : ValExpr) (_τ : CppType) : Prop :=
  True

/-- Placeholder for replaying an ordinary place used by the selected tail. -/
def SeqTailPlaceUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_p : PlaceExpr) (_τ : CppType) : Prop :=
  True

/--
Ordinary read replay slots for tail expressions and places.

The fields are already shaped for later materialization into
`ExprReadyConcrete` / `PlaceReadyConcrete`; the placeholder predicates can be
strengthened without changing this route-level interface.
-/
structure SeqTailOrdinaryReadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  valueUse :
    ∀ {e : ValExpr} {τ : CppType},
      SeqTailValueUseReplayAtRouteCI route e τ
  placeUse :
    ∀ {p : PlaceExpr} {τ : CppType},
      SeqTailPlaceUseReplayAtRouteCI route p τ

namespace SeqTailOrdinaryReadReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailOrdinaryReadReplayAtRouteCI route :=
  { valueUse := by
      intro e τ
      trivial
    placeUse := by
      intro p τ
      trivial }

end SeqTailOrdinaryReadReplayAtRouteCI

/--
Placeholder for replaying a pointer expression used by a tail dereference after
the selected route.

Future refinement target:
replace `True` by the data needed for `PlaceReadyConcrete.deref`, namely

* the pointer expression has pointer type;
* it evaluates in the post-state to an address;
* the addressed cell is live and typed.
-/
def SeqTailDerefUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_e : ValExpr) (_τ : CppType) : Prop :=
  True

/--
Pointer-dereference replay slots.

This is shaped for the `PlaceReadyConcrete.deref` constructor.  The field is
still coarse, but `e` and `τ` are now part of a named predicate, so later we can
strengthen the predicate without changing the route-level API.
-/
structure SeqTailDerefPointerReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  derefUse :
    ∀ {e : ValExpr} {τ : CppType},
      SeqTailDerefUseReplayAtRouteCI route e τ

namespace SeqTailDerefPointerReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailDerefPointerReplayAtRouteCI route :=
  { derefUse := by
      intro e τ
      trivial }

end SeqTailDerefPointerReplayAtRouteCI

/--
Placeholder for replaying a loaded place after the selected route.

Future refinement target:
replace `True` by the data needed for `ExprReadyConcrete.load`, namely

* the place is ready in the post-state;
* it evaluates to an address;
* the addressed cell is readable and typed.
-/
def SeqTailLoadUseReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (_p : PlaceExpr) (_τ : CppType) : Prop :=
  True

/--
Load-readability replay slots.

This is shaped for the `ExprReadyConcrete.load` constructor.  The field is still
coarse, but `p` and `τ` are now part of a named predicate, so later we can
strengthen the predicate without changing the route-level API.
-/
structure SeqTailLoadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  loadUse :
    ∀ {p : PlaceExpr} {τ : CppType},
      SeqTailLoadUseReplayAtRouteCI route p τ

namespace SeqTailLoadReplayAtRouteCI

/-- Coarse compatibility inhabitant for old paths. -/
def trivial
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P} :
    SeqTailLoadReplayAtRouteCI route :=
  { loadUse := by
      intro p τ
      trivial }

end SeqTailLoadReplayAtRouteCI

end Cpp
