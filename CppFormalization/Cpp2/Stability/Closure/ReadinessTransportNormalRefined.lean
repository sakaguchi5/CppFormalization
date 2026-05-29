import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalEnvPreserving
import CppFormalization.Cpp2.Stability.Closure.ReadinessTransportNormalEnvExtendingOldNames

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalRefined

Refined surface for replacing the old unrestricted
` 削除済み` debt.

The old core bundles four unrestricted transport goals:
- place readiness transport
- expression readiness transport
- statement readiness transport
- block readiness transport

That shape is useful as a temporary choke point, but it is too coarse as a
final theorem target.  In particular, env-extending heads such as
`declareObj` and `declareRef` change the meaning of the freshly introduced
name.  Old names should be transported; the fresh name should be introduced
from the post-state binding; and load/read readiness must be guarded by an
explicit readable/initialized condition.

This file intentionally contains only refined vocabulary and obligation
surfaces.  It does not introduce any axiom.
-/

/- =========================================================
   1. Syntactic old-name target classes
   ========================================================= -/

mutual

/-- A place expression does not mention the freshly introduced identifier. -/
inductive PlaceDoesNotMentionIdent : Ident → PlaceExpr → Prop where
  | var {fresh y : Ident} :
      y ≠ fresh →
      PlaceDoesNotMentionIdent fresh (.var y)
  | deref {fresh : Ident} {e : ValExpr} :
      ExprDoesNotMentionIdent fresh e →
      PlaceDoesNotMentionIdent fresh (.deref e)

/-- A value expression does not mention the freshly introduced identifier. -/
inductive ExprDoesNotMentionIdent : Ident → ValExpr → Prop where
  | litBool {fresh : Ident} {b : Bool} :
      ExprDoesNotMentionIdent fresh (.litBool b)
  | litInt {fresh : Ident} {n : Int} :
      ExprDoesNotMentionIdent fresh (.litInt n)
  | load {fresh : Ident} {p : PlaceExpr} :
      PlaceDoesNotMentionIdent fresh p →
      ExprDoesNotMentionIdent fresh (.load p)
  | addrOf {fresh : Ident} {p : PlaceExpr} :
      PlaceDoesNotMentionIdent fresh p →
      ExprDoesNotMentionIdent fresh (.addrOf p)
  | add {fresh : Ident} {e₁ e₂ : ValExpr} :
      ExprDoesNotMentionIdent fresh e₁ →
      ExprDoesNotMentionIdent fresh e₂ →
      ExprDoesNotMentionIdent fresh (.add e₁ e₂)
  | sub {fresh : Ident} {e₁ e₂ : ValExpr} :
      ExprDoesNotMentionIdent fresh e₁ →
      ExprDoesNotMentionIdent fresh e₂ →
      ExprDoesNotMentionIdent fresh (.sub e₁ e₂)
  | mul {fresh : Ident} {e₁ e₂ : ValExpr} :
      ExprDoesNotMentionIdent fresh e₁ →
      ExprDoesNotMentionIdent fresh e₂ →
      ExprDoesNotMentionIdent fresh (.mul e₁ e₂)
  | eq {fresh : Ident} {e₁ e₂ : ValExpr} :
      ExprDoesNotMentionIdent fresh e₁ →
      ExprDoesNotMentionIdent fresh e₂ →
      ExprDoesNotMentionIdent fresh (.eq e₁ e₂)
  | lt {fresh : Ident} {e₁ e₂ : ValExpr} :
      ExprDoesNotMentionIdent fresh e₁ →
      ExprDoesNotMentionIdent fresh e₂ →
      ExprDoesNotMentionIdent fresh (.lt e₁ e₂)
  | not {fresh : Ident} {e : ValExpr} :
      ExprDoesNotMentionIdent fresh e →
      ExprDoesNotMentionIdent fresh (.not e)

/-- A statement does not mention the freshly introduced identifier. -/
inductive StmtDoesNotMentionIdent : Ident → CppStmt → Prop where
  | skip {fresh : Ident} :
      StmtDoesNotMentionIdent fresh .skip
  | exprStmt {fresh : Ident} {e : ValExpr} :
      ExprDoesNotMentionIdent fresh e →
      StmtDoesNotMentionIdent fresh (.exprStmt e)
  | assign {fresh : Ident} {p : PlaceExpr} {e : ValExpr} :
      PlaceDoesNotMentionIdent fresh p →
      ExprDoesNotMentionIdent fresh e →
      StmtDoesNotMentionIdent fresh (.assign p e)
  | declareObjNone {fresh y : Ident} {τ : CppType} :
      y ≠ fresh →
      StmtDoesNotMentionIdent fresh (.declareObj τ y none)
  | declareObjSome {fresh y : Ident} {τ : CppType} {e : ValExpr} :
      y ≠ fresh →
      ExprDoesNotMentionIdent fresh e →
      StmtDoesNotMentionIdent fresh (.declareObj τ y (some e))
  | declareRef {fresh y : Ident} {τ : CppType} {p : PlaceExpr} :
      y ≠ fresh →
      PlaceDoesNotMentionIdent fresh p →
      StmtDoesNotMentionIdent fresh (.declareRef τ y p)
  | seq {fresh : Ident} {s t : CppStmt} :
      StmtDoesNotMentionIdent fresh s →
      StmtDoesNotMentionIdent fresh t →
      StmtDoesNotMentionIdent fresh (.seq s t)
  | ite {fresh : Ident} {c : ValExpr} {s t : CppStmt} :
      ExprDoesNotMentionIdent fresh c →
      StmtDoesNotMentionIdent fresh s →
      StmtDoesNotMentionIdent fresh t →
      StmtDoesNotMentionIdent fresh (.ite c s t)
  | whileStmt {fresh : Ident} {c : ValExpr} {body : CppStmt} :
      ExprDoesNotMentionIdent fresh c →
      StmtDoesNotMentionIdent fresh body →
      StmtDoesNotMentionIdent fresh (.whileStmt c body)
  | block {fresh : Ident} {ss : StmtBlock} :
      BlockDoesNotMentionIdent fresh ss →
      StmtDoesNotMentionIdent fresh (.block ss)
  | breakStmt {fresh : Ident} :
      StmtDoesNotMentionIdent fresh .breakStmt
  | continueStmt {fresh : Ident} :
      StmtDoesNotMentionIdent fresh .continueStmt
  | returnNone {fresh : Ident} :
      StmtDoesNotMentionIdent fresh (.returnStmt none)
  | returnSome {fresh : Ident} {e : ValExpr} :
      ExprDoesNotMentionIdent fresh e →
      StmtDoesNotMentionIdent fresh (.returnStmt (some e))

/-- A block does not mention the freshly introduced identifier. -/
inductive BlockDoesNotMentionIdent : Ident → StmtBlock → Prop where
  | nil {fresh : Ident} :
      BlockDoesNotMentionIdent fresh .nil
  | cons {fresh : Ident} {s : CppStmt} {ss : StmtBlock} :
      StmtDoesNotMentionIdent fresh s →
      BlockDoesNotMentionIdent fresh ss →
      BlockDoesNotMentionIdent fresh (.cons s ss)

end

/- =========================================================
   2. Refined old-name transport obligations
   ========================================================= -/

abbrev EnvExtendingOldNamePlaceTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) (fresh : Ident) : Prop :=
  ∀ {p : PlaceExpr} {τ : CppType},
    PlaceDoesNotMentionIdent fresh p →
    NormalTransportCtx Γ Δ σ σ' head →
    HasPlaceType Δ p τ →
    PlaceReadyConcrete Γ σ p τ →
    PlaceReadyConcrete Δ σ' p τ

abbrev EnvExtendingOldNameExprTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) (fresh : Ident) : Prop :=
  ∀ {e : ValExpr} {τ : CppType},
    ExprDoesNotMentionIdent fresh e →
    NormalTransportCtx Γ Δ σ σ' head →
    HasValueType Δ e τ →
    ExprReadyConcrete Γ σ e τ →
    ExprReadyConcrete Δ σ' e τ

abbrev EnvExtendingOldNameStmtTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) (fresh : Ident) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {st : CppStmt},
    StmtDoesNotMentionIdent fresh st →
    NormalTransportCtx Γ Δ σ σ' head →
    HasTypeStmtCI k Δ st Ω →
    StmtReadyConcrete Γ σ st →
    StmtReadyConcrete Δ σ' st

abbrev EnvExtendingOldNameBlockTransportGoal
    (Γ Δ : TypeEnv) (σ σ' : State) (head : CppStmt) (fresh : Ident) : Prop :=
  ∀ {k : ControlKind} {Ω : TypeEnv} {ss : StmtBlock},
    BlockDoesNotMentionIdent fresh ss →
    NormalTransportCtx Γ Δ σ σ' head →
    HasTypeBlockCI k Δ ss Ω →
    BlockReadyConcrete Γ σ ss →
    BlockReadyConcrete Δ σ' ss

/- Declaration-specialized old-name obligations. -/

abbrev DeclareObjOldNameStmtTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option ValExpr) : Prop :=
  EnvExtendingOldNameStmtTransportGoal
    Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) x

abbrev DeclareObjOldNameBlockTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option ValExpr) : Prop :=
  EnvExtendingOldNameBlockTransportGoal
    Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) x

abbrev DeclareRefOldNameStmtTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (p0 : PlaceExpr) : Prop :=
  EnvExtendingOldNameStmtTransportGoal
    Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) x

abbrev DeclareRefOldNameBlockTransportGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (p0 : PlaceExpr) : Prop :=
  EnvExtendingOldNameBlockTransportGoal
    Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) x

/- =========================================================
   3. Fresh-name introduction obligations
   ========================================================= -/

/--
Fresh object place readiness is not a transport theorem: it must be introduced
from the post-state binding created by `declareObj`.
-/
abbrev DeclareObjFreshObjectPlaceIntroGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option ValExpr) : Prop :=
  NormalTransportCtx Γ (declareTypeObject Γ x τ) σ σ' (.declareObj τ x ov) →
  PlaceReadyConcrete (declareTypeObject Γ x τ) σ' (.var x) τ

/--
Fresh reference place readiness is likewise introduced from the post-state ref
binding created by `declareRef`.
-/
abbrev DeclareRefFreshPlaceIntroGoal
    (Γ : TypeEnv) (σ σ' : State) (τ : CppType) (x : Ident) (p0 : PlaceExpr) : Prop :=
  NormalTransportCtx Γ (declareTypeRef Γ x τ) σ σ' (.declareRef τ x p0) →
  PlaceReadyConcrete (declareTypeRef Γ x τ) σ' (.var x) τ

/- =========================================================
   4. Read/load condition discipline
   ========================================================= -/

/--
A generic theorem-backed read introduction: load-readiness is available only
when the place is ready and the target cell is explicitly readable.

This is the small local rule that prevents the fresh-name story from claiming
that `declareObj τ x none` makes `load x` ready.
-/
theorem readinessTransportRefined_load_ready_of_place_and_readable
    {Γ : TypeEnv} {σ : State} {p : PlaceExpr} {τ : CppType} {a : Nat}
    (hp : PlaceReadyConcrete Γ σ p τ)
    (hplace : BigStepPlace σ p a)
    (hread : CellReadableTyped σ a τ) :
    ExprReadyConcrete Γ σ (.load p) τ := by
  exact ExprReadyConcrete.load hp ⟨a, hplace, hread⟩

/- =========================================================
   5. Refined surface bundle
   ========================================================= -/

/--
Refined replacement surface for the old unrestricted core.

This is not instantiated yet.  It records the theorem targets that should
replace the coarse ` 削除済み` over time.
-/
structure ReadinessTransportNormalRefinedSurface : Type where
  envPreserving : ReadinessTransportNormalEnvPreservingFragment
  envExtendingOldNames : ReadinessTransportNormalEnvExtendingOldNameFragment

  declareObjOldStmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjOldNameStmtTransportGoal Γ σ σ' τ x ov

  declareObjOldBlockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjOldNameBlockTransportGoal Γ σ σ' τ x ov

  declareRefOldStmtTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefOldNameStmtTransportGoal Γ σ σ' τ x p0

  declareRefOldBlockTransport :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefOldNameBlockTransportGoal Γ σ σ' τ x p0

  declareObjFreshObjectPlaceIntro :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option ValExpr},
      DeclareObjFreshObjectPlaceIntroGoal Γ σ σ' τ x ov

  declareRefFreshPlaceIntro :
    ∀ {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr},
      DeclareRefFreshPlaceIntroGoal Γ σ σ' τ x p0

end Cpp
