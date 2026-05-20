import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Stability

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: contract explanation surface

This file is intentionally *not* another fallback layer.

The core files provide the compact proof kernel:

* `PlaceReplay`
* `ValueReplay`
* `BlockReplay`
* `StmtReplay`
* `Package`
* `StabilityAtRoute`

That core is mathematically clean, but it hides some C++-facing contract labels.
This module restores those labels as a thin explanation surface.  Every surface
predicate below lowers to the core replay predicates; no broad axiom and no
`True` placeholder is introduced here.
-/

/- =========================================================
   Control-only tails
   ========================================================= -/

/--
Tail statements that need no runtime replay contract.

These are control-only constructors: once the selected route reaches the tail,
readiness follows from the statement constructor itself.
-/
inductive ControlOnlyTail
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | skip :
      ControlOnlyTail route .skip
  | breakStmt :
      ControlOnlyTail route .breakStmt
  | continueStmt :
      ControlOnlyTail route .continueStmt
  | returnNone :
      ControlOnlyTail route (.returnStmt none)

namespace ControlOnlyTail

/-- Control-only tails lower directly to statement replay. -/
theorem toStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : ControlOnlyTail route st) :
    StmtReplay route st := by
  cases h with
  | skip =>
      exact StmtReplay.skip
  | breakStmt =>
      exact StmtReplay.breakStmt
  | continueStmt =>
      exact StmtReplay.continueStmt
  | returnNone =>
      exact StmtReplay.returnNone

end ControlOnlyTail

/- =========================================================
   Pure value expressions: no memory access
   ========================================================= -/

/--
Pure value expressions that need no heap, binding, load-readability, or pointer
contract.

This is the C++ explanation layer for expressions such as literals and pure
arithmetic/comparison/boolean combinations.
-/
inductive PureValueNoMemory
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    ValExpr → CppType → Prop where
  | litBool {b : Bool} :
      PureValueNoMemory route (.litBool b) (.base .bool)
  | litInt {n : Int} :
      PureValueNoMemory route (.litInt n) (.base .int)
  | add {e₁ e₂ : ValExpr} :
      PureValueNoMemory route e₁ (.base .int) →
      PureValueNoMemory route e₂ (.base .int) →
      PureValueNoMemory route (.add e₁ e₂) (.base .int)
  | sub {e₁ e₂ : ValExpr} :
      PureValueNoMemory route e₁ (.base .int) →
      PureValueNoMemory route e₂ (.base .int) →
      PureValueNoMemory route (.sub e₁ e₂) (.base .int)
  | mul {e₁ e₂ : ValExpr} :
      PureValueNoMemory route e₁ (.base .int) →
      PureValueNoMemory route e₂ (.base .int) →
      PureValueNoMemory route (.mul e₁ e₂) (.base .int)
  | eq {e₁ e₂ : ValExpr} {τ : CppType} :
      PureValueNoMemory route e₁ τ →
      PureValueNoMemory route e₂ τ →
      PureValueNoMemory route (.eq e₁ e₂) (.base .bool)
  | lt {e₁ e₂ : ValExpr} :
      PureValueNoMemory route e₁ (.base .int) →
      PureValueNoMemory route e₂ (.base .int) →
      PureValueNoMemory route (.lt e₁ e₂) (.base .bool)
  | not {e : ValExpr} :
      PureValueNoMemory route e (.base .bool) →
      PureValueNoMemory route (.not e) (.base .bool)

namespace PureValueNoMemory

/-- Pure no-memory expressions lower to value replay. -/
theorem toValueReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : PureValueNoMemory route e τ) :
    ValueReplay route e τ := by
  induction h with
  | litBool =>
      exact ValueReplay.litBool
  | litInt =>
      exact ValueReplay.litInt
  | add _h₁ _h₂ ih₁ ih₂ =>
      exact ValueReplay.add ih₁ ih₂
  | sub _h₁ _h₂ ih₁ ih₂ =>
      exact ValueReplay.sub ih₁ ih₂
  | mul _h₁ _h₂ ih₁ ih₂ =>
      exact ValueReplay.mul ih₁ ih₂
  | eq _h₁ _h₂ ih₁ ih₂ =>
      exact ValueReplay.eq ih₁ ih₂
  | lt _h₁ _h₂ ih₁ ih₂ =>
      exact ValueReplay.lt ih₁ ih₂
  | not _h ih =>
      exact ValueReplay.not ih

end PureValueNoMemory

/- =========================================================
   Ordinary place stability
   ========================================================= -/

/--
Ordinary name/binding stability for tail places.

This is the surface contract saying: after the selected left-normal route, an
ordinary variable place still resolves to a live typed object/reference cell.
-/
inductive OrdinaryPlaceStability
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    PlaceExpr → CppType → Prop where
  | varObject
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.object τ) →
      lookupBinding σ1 x = some (.object τ a) →
      CellLiveTyped σ1 a τ →
      OrdinaryPlaceStability route (.var x) τ
  | varRef
      {x : Ident} {τ : CppType} {a : Nat} :
      lookupDecl route.Θ x = some (.ref τ) →
      lookupBinding σ1 x = some (.ref τ a) →
      CellLiveTyped σ1 a τ →
      OrdinaryPlaceStability route (.var x) τ

namespace OrdinaryPlaceStability

/-- Ordinary place stability lowers to place replay. -/
theorem toPlaceReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : OrdinaryPlaceStability route p τ) :
    PlaceReplay route p τ := by
  cases h with
  | varObject hdecl hbind hlive =>
      exact PlaceReplay.varObject hdecl hbind hlive
  | varRef hdecl hbind hlive =>
      exact PlaceReplay.varRef hdecl hbind hlive

end OrdinaryPlaceStability

/- =========================================================
   Pointer/dereference stability
   ========================================================= -/

/--
Pointer dereference stability for a tail dereference place.

This is the C++ contract saying: the pointer expression is ready as a pointer
value in the selected post-state, and the addressed cell is still live and typed.
-/
inductive PointerDerefStability
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (e : ValExpr) (τ : CppType) : Prop where
  | mk
      {a : Nat} :
      PtrValueReadyAt route.Θ σ1 e τ a →
      CellLiveTyped σ1 a τ →
      PointerDerefStability route e τ

namespace PointerDerefStability

/-- Pointer/deref stability lowers to place replay for `*e`. -/
theorem toPlaceReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {e : ValExpr} {τ : CppType}
    (h : PointerDerefStability route e τ) :
    PlaceReplay route (.deref e) τ := by
  cases h with
  | mk hptr hlive =>
      exact PlaceReplay.deref hptr hlive

end PointerDerefStability

/- =========================================================
   Load readability
   ========================================================= -/

/--
Load-readability contract for a tail load.

This is the C++ contract saying: the source place is replay-ready, evaluates in
the selected post-state to an address, and the addressed cell is readable and
well-typed.
-/
structure LoadReadability
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (p : PlaceExpr) (τ : CppType) : Prop where
  place : PlaceReplay route p τ
  readable : ∃ a, BigStepPlace σ1 p a ∧ CellReadableTyped σ1 a τ

namespace LoadReadability

/-- Load-readability lowers to value replay for `load p`. -/
theorem toValueReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : LoadReadability route p τ) :
    ValueReplay route (.load p) τ :=
  ValueReplay.load h.place h.readable

end LoadReadability

/- =========================================================
   Address-of stability
   ========================================================= -/

/--
Address-of contract for a tail address expression.

Taking an address does not read the target cell, but the place itself must be
ready in the selected post-state.
-/
structure AddressOfStability
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (p : PlaceExpr) (τ : CppType) : Prop where
  place : PlaceReplay route p τ

namespace AddressOfStability

/-- Address-of stability lowers to value replay for `&p`. -/
theorem toValueReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {p : PlaceExpr} {τ : CppType}
    (h : AddressOfStability route p τ) :
    ValueReplay route (.addrOf p) (.ptr τ) :=
  ValueReplay.addrOf h.place

end AddressOfStability

/- =========================================================
   Declaration freshness / initialization contracts
   ========================================================= -/

/--
Declaration-specific surface contracts.

These are the C++-facing obligations for declaration tails: the declared name is
fresh in the current type scope, the declared object type is valid when needed,
and initializer/reference operands replay in the selected post-state.
-/
inductive DeclarationContract
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | declareObjNone
      {τ : CppType} {x : Ident} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      DeclarationContract route (.declareObj τ x none)
  | declareObjSome
      {τ : CppType} {x : Ident} {e : ValExpr} :
      currentTypeScopeFresh route.Θ x →
      ObjectType τ →
      ValueReplay route e τ →
      DeclarationContract route (.declareObj τ x (some e))
  | declareRef
      {τ : CppType} {x : Ident} {p : PlaceExpr} :
      currentTypeScopeFresh route.Θ x →
      PlaceReplay route p τ →
      DeclarationContract route (.declareRef τ x p)

namespace DeclarationContract

/-- Declaration contracts lower to statement replay. -/
theorem toStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : DeclarationContract route st) :
    StmtReplay route st := by
  cases h with
  | declareObjNone hfresh hobj =>
      exact StmtReplay.declareObjNone hfresh hobj
  | declareObjSome hfresh hobj hvalue =>
      exact StmtReplay.declareObjSome hfresh hobj hvalue
  | declareRef hfresh hplace =>
      exact StmtReplay.declareRef hfresh hplace

end DeclarationContract

/- =========================================================
   Block surface
   ========================================================= -/

/--
Block surface contract.

For now, this mirrors the clean core: each head statement of the opened block is
ready under the pushed type/runtime scopes.  A future block-tail replay theory
can refine this without changing the seq-tail statement surface.
-/
inductive SurfaceBlock
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    StmtBlock → Prop where
  | nil :
      SurfaceBlock route .nil
  | cons
      {st : CppStmt} {ss : StmtBlock} :
      StmtReadyConcrete (pushTypeScope route.Θ) (pushScope σ1) st →
      SurfaceBlock route ss →
      SurfaceBlock route (.cons st ss)

namespace SurfaceBlock

/-- Block surface contracts lower to block replay. -/
theorem toBlockReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {ss : StmtBlock}
    (h : SurfaceBlock route ss) :
    BlockReplay route ss := by
  induction h with
  | nil =>
      exact BlockReplay.nil
  | cons hst _hss ih =>
      exact BlockReplay.cons hst ih

end SurfaceBlock

/- =========================================================
   Statement surface
   ========================================================= -/

/--
C++-facing statement surface for seq-tail replay.

This is an explanation-oriented layer.  It groups the compact `StmtReplay` core
under contract names that correspond to C++ safety concerns.
-/
inductive SurfaceStmt
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    CppStmt → Prop where
  | control
      {st : CppStmt} :
      ControlOnlyTail route st →
      SurfaceStmt route st
  | declaration
      {st : CppStmt} :
      DeclarationContract route st →
      SurfaceStmt route st
  | exprStmt
      {e : ValExpr} {τ : CppType} :
      ValueReplay route e τ →
      SurfaceStmt route (.exprStmt e)
  | assign
      {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      PlaceReplay route p τ →
      ValueReplay route e τ →
      SurfaceStmt route (.assign p e)
  | seq
      {u v : CppStmt} :
      SurfaceStmt route u →
      SurfaceStmt route v →
      SurfaceStmt route (.seq u v)
  | ite
      {c : ValExpr} {u v : CppStmt} :
      ValueReplay route c (.base .bool) →
      SurfaceStmt route u →
      SurfaceStmt route v →
      SurfaceStmt route (.ite c u v)
  | whileStmt
      {c : ValExpr} {body : CppStmt} :
      ValueReplay route c (.base .bool) →
      SurfaceStmt route body →
      SurfaceStmt route (.whileStmt c body)
  | block
      {ss : StmtBlock} :
      SurfaceBlock route ss →
      SurfaceStmt route (.block ss)
  | returnSome
      {e : ValExpr} {τ : CppType} :
      ValueReplay route e τ →
      SurfaceStmt route (.returnStmt (some e))

namespace SurfaceStmt

/-- Surface statements lower to the compact statement replay core. -/
theorem toStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : SurfaceStmt route st) :
    StmtReplay route st := by
  induction h with
  | control hcontrol =>
      exact hcontrol.toStmtReplay
  | declaration hdecl =>
      exact hdecl.toStmtReplay
  | exprStmt hvalue =>
      exact StmtReplay.exprStmt hvalue
  | assign hplace hvalue =>
      exact StmtReplay.assign hplace hvalue
  | seq _hu _hv ihU ihV =>
      exact StmtReplay.seq ihU ihV
  | ite hc _hu _hv ihU ihV =>
      exact StmtReplay.ite hc ihU ihV
  | whileStmt hc _hbody ihBody =>
      exact StmtReplay.whileStmt hc ihBody
  | block hblock =>
      exact StmtReplay.block hblock.toBlockReplay
  | returnSome hvalue =>
      exact StmtReplay.returnSome hvalue

/-- Surface statements materialize concrete post-state readiness. -/
theorem ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    {st : CppStmt}
    (h : SurfaceStmt route st) :
    StmtReadyConcrete route.Θ σ1 st :=
  h.toStmtReplay.ready

end SurfaceStmt

/- =========================================================
   Surface packages
   ========================================================= -/

/--
A C++-facing surface package sufficient to start the tail continuation.
-/
structure SurfacePackage
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  postState : PostState route
  surface : SurfaceStmt route t

namespace SurfacePackage

/-- Forget the explanation surface to the compact replay package. -/
def toPackage
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SurfacePackage route) :
    Package route :=
  { postState := h.postState
    replay := h.surface.toStmtReplay }

/-- Dynamic continuation boundary induced by the surface package. -/
def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SurfacePackage route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  h.toPackage.toDynamicBoundary

/-- Route-local stability induced by the surface package. -/
def toStabilityAtRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SurfacePackage route) :
    StabilityAtRoute route :=
  { postState := h.postState
    replay := h.surface.toStmtReplay }

end SurfacePackage

end SeqTailReplay2
end Cpp
