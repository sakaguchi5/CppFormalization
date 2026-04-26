import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.External.ObjectDeclRuntimeBridgeV3
import CppFormalization.Cpp2.Closure.Transitions.DeclareObject.Preservation
import CppFormalization.Cpp2.Closure.Foundation.CoreBigStepFragment
import CppFormalization.Cpp2.Closure.Foundation.WellFormedFromTyping
import CppFormalization.Cpp2.Closure.Foundation.TopFrameWitness

namespace Cpp

/-
# Closure.External.ObjectDeclStdFragmentV3

Concrete theorem-backed std/runtime fragment for object-declaration statements.

The key point of this version is that initializer coherence is carried by an
inductive certificate (`ObjectDeclRuntimeInit`) instead of dependent `match`
fields on `ObjectDeclRuntimeCert`.  This mirrors the `BodyRootCoherent` repair:
the constructor records the coherent shape, and projections are recovered by
small eliminators.
-/

/--
Runtime-side initializer certificate for object declarations.

`noInit` says there is no initializer and no stored value.
`someInit` says the initializer is typed/ready, evaluates to the stored value,
and that stored value is compatible with the declared object type.
-/
inductive ObjectDeclRuntimeInit
    (Γ : TypeEnv) (σ : State) (τ : CppType) :
    Option ValExpr → Option Value → Type where
  | noInit :
      ObjectDeclRuntimeInit Γ σ τ (Option.none : Option ValExpr) (Option.none : Option Value)
  | someInit {e : ValExpr} {v : Value} :
      HasValueType Γ e τ →
      ExprReadyConcrete Γ σ e τ →
      BigStepValue σ e v →
      ValueCompat v τ →
      ObjectDeclRuntimeInit Γ σ τ (Option.some e) (Option.some v)

namespace ObjectDeclRuntimeInit

def toStoredValue
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {initExpr : Option ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ initExpr ov) :
    ObjectDeclInitStoredValue σ τ initExpr ov := by
  cases h with
  | noInit =>
      exact ObjectDeclInitStoredValue.intro_none
  | someInit hty hre hstep hcompat =>
      exact ObjectDeclInitStoredValue.intro_some hstep hcompat

@[simp] theorem ov_eq_none
    {Γ : TypeEnv} {σ : State} {τ : CppType} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.none : Option ValExpr) ov) :
    ov = Option.none := by
  cases h
  rfl

def someWitness
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    {v : Value //
      ov = Option.some v ∧
      HasValueType Γ e τ ∧
      ExprReadyConcrete Γ σ e τ ∧
      BigStepValue σ e v ∧
      ValueCompat v τ} := by
  cases h with
  | someInit hty hre hstep hcompat =>
      exact ⟨_, rfl, hty, hre, hstep, hcompat⟩

theorem ov_is_some
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    ∃ v, ov = Option.some v := by
  exact ⟨(someWitness h).1, (someWitness h).2.1⟩

def hasValueType
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    HasValueType Γ e τ :=
  (someWitness h).2.2.1

def exprReady
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    ExprReadyConcrete Γ σ e τ :=
  (someWitness h).2.2.2.1

def bigStepValue
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    BigStepValue σ e (someWitness h).1 :=
  (someWitness h).2.2.2.2.1

def valueCompat
    {Γ : TypeEnv} {σ : State} {τ : CppType}
    {e : ValExpr} {ov : Option Value}
    (h : ObjectDeclRuntimeInit Γ σ τ (Option.some e) ov) :
    ValueCompat (someWitness h).1 τ :=
  (someWitness h).2.2.2.2.2

end ObjectDeclRuntimeInit

/-- Runtime-side certificate for an object-declaration statement. -/
structure ObjectDeclRuntimeCert where
  Γ : TypeEnv
  σ : State
  x : Ident
  τ : CppType
  ov : Option Value
  initExpr : Option ValExpr
  init : ObjectDeclRuntimeInit Γ σ τ initExpr ov
  ready : DeclareObjectReadyRecomputed Γ σ x τ ov
  objTy : ObjectType τ

namespace ObjectDeclRuntimeCert

@[simp] def targetStmt (c : ObjectDeclRuntimeCert) : CppStmt :=
  .declareObj c.τ c.x c.initExpr

def initStored (c : ObjectDeclRuntimeCert) :
    ObjectDeclInitStoredValue c.σ c.τ c.initExpr c.ov :=
  c.init.toStoredValue

@[simp] theorem targetStmt_none
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {hinit : ObjectDeclRuntimeInit Γ σ τ (Option.none : Option ValExpr) (Option.none : Option Value)}
    {h : DeclareObjectReadyRecomputed Γ σ x τ (Option.none : Option Value)}
    {hobj : ObjectType τ} :
    (ObjectDeclRuntimeCert.mk Γ σ x τ Option.none Option.none hinit h hobj).targetStmt =
      .declareObj τ x none := rfl

@[simp] theorem targetStmt_some
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType}
    {e : ValExpr} {v : Value}
    {hinit : ObjectDeclRuntimeInit Γ σ τ (Option.some e) (Option.some v)}
    {h : DeclareObjectReadyRecomputed Γ σ x τ (Option.some v)}
    {hobj : ObjectType τ} :
    (ObjectDeclRuntimeCert.mk Γ σ x τ (Option.some v) (Option.some e) hinit h hobj).targetStmt =
      .declareObj τ x (some e) := rfl

/-- 初期化式がある場合、その型が τ であることを抽出する。 -/
def getHasValueType (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) : HasValueType c.Γ e c.τ := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases h_expr
  exact ObjectDeclRuntimeInit.hasValueType init

/-- 初期化式がある場合、その readiness を抽出する。 -/
def getExprReady (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) : ExprReadyConcrete c.Γ c.σ e c.τ := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases h_expr
  exact ObjectDeclRuntimeInit.exprReady init

@[simp] theorem ov_eq_none_of_init_none
    {c : ObjectDeclRuntimeCert} (hinit : c.initExpr = none) :
    c.ov = none := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases hinit
  exact ObjectDeclRuntimeInit.ov_eq_none init

/-- 初期化式がある場合、その式が最終的に格納する concrete value を subtype として抽出する。 -/
def getStoredValueWitness (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) :
    {v : Value // c.ov = some v ∧ BigStepValue c.σ e v ∧ ValueCompat v c.τ} := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases h_expr
  let w := ObjectDeclRuntimeInit.someWitness init
  exact
    ⟨ w.1
    , w.2.1
    , w.2.2.2.2.1
    , w.2.2.2.2.2 ⟩

/-- Prop 版の存在定理。データ抽出ではなく、証明用。 -/
theorem getStoredValue (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) :
    ∃ v, c.ov = some v ∧ BigStepValue c.σ e v ∧ ValueCompat v c.τ := by
  let w := c.getStoredValueWitness h_expr
  exact ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩

/-- 初期化式がある場合の stored-value witness を subtype として取り出す。 -/
def storedValueWitness (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (hinit : c.initExpr = some e) :
    {v : Value // c.ov = some v ∧ BigStepValue c.σ e v ∧ ValueCompat v c.τ} :=
  c.getStoredValueWitness hinit

/-- 初期化式がある場合、ov は必ず some v になる。 -/
theorem ov_is_some_of_init_some {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) : ∃ v, c.ov = some v := by
  rcases c.getStoredValue hinit with ⟨v, h_ov, _, _⟩
  exact ⟨v, h_ov⟩

@[simp] theorem ov_ne_none_of_init_some
    {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) :
    c.ov ≠ none := by
  rcases c.getStoredValue hinit with ⟨v, hov, _, _⟩
  simp [hov]

@[simp] theorem storedValueWitness_ov
    {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) :
    c.ov = some (c.storedValueWitness hinit).1 :=
  (c.storedValueWitness hinit).2.1

@[simp] theorem storedValueWitness_bigStep
    {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) :
    BigStepValue c.σ e (c.storedValueWitness hinit).1 :=
  (c.storedValueWitness hinit).2.2.1

@[simp] theorem storedValueWitness_compat
    {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) :
    ValueCompat (c.storedValueWitness hinit).1 c.τ :=
  (c.storedValueWitness hinit).2.2.2

def stmtReadyConcrete (c : ObjectDeclRuntimeCert) :
    StmtReadyConcrete c.Γ c.σ c.targetStmt := by
  cases hinit : c.initExpr with
  | none =>
      have hov : c.ov = none := c.ov_eq_none_of_init_none hinit
      have hreadyNone : DeclareObjectReadyRecomputed c.Γ c.σ c.x c.τ none := by
        simpa [hov] using c.ready
      simpa [ObjectDeclRuntimeCert.targetStmt, hinit] using
        DeclareObjectReadyRecomputed.toStmtReadyConcrete_declareObjNone
          hreadyNone c.objTy
  | some e =>
      have hty : HasValueType c.Γ e c.τ := c.getHasValueType hinit
      have hre : ExprReadyConcrete c.Γ c.σ e c.τ := c.getExprReady hinit
      simpa [ObjectDeclRuntimeCert.targetStmt, hinit] using
        DeclareObjectReadyRecomputed.toStmtReadyConcrete_declareObjSome
          (h := c.ready) c.objTy hty hre

def bodyDynamicBoundary (c : ObjectDeclRuntimeCert) :
    BodyDynamicBoundary c.Γ c.σ c.targetStmt := by
  exact BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
    ((c.ready).ready).concrete
    c.stmtReadyConcrete

theorem bodyDynamicBoundary_eq_target
    (c : ObjectDeclRuntimeCert) :
    BodyDynamicBoundary c.Γ c.σ c.targetStmt :=
  c.bodyDynamicBoundary

def mkRuntime_none {n : ObjectDeclRuntimeCert} (hinit : n.initExpr = none) :
    RuntimePiecesV3 n.Γ n.σ (.declareObj n.τ n.x none) := by
  rcases n with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases hinit
  have hov : ov = none := ObjectDeclRuntimeInit.ov_eq_none init
  subst hov
  exact DeclareObjectReadyRecomputed.runtimePieces_declareObjNone ready objTy

def mkRuntime_some {n : ObjectDeclRuntimeCert} {e : ValExpr} (hinit : n.initExpr = some e) :
    RuntimePiecesV3 n.Γ n.σ (.declareObj n.τ n.x (some e)) := by
  rcases n with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases hinit
  exact DeclareObjectReadyRecomputed.runtimePieces_declareObjSome
    ready objTy
    (ObjectDeclRuntimeInit.hasValueType init)
    (ObjectDeclRuntimeInit.exprReady init)

end ObjectDeclRuntimeCert

/-- The theorem-backed std/runtime fragment specialized to object declarations. -/
def objectDeclStdFragmentV3 : VerifiedStdFragmentV3 where
  Name := ObjectDeclRuntimeCert
  uses := fun _ => True
  supportsRuntime := fun n Γ σ st =>
    Γ = n.Γ ∧ σ = n.σ ∧ st = n.targetStmt
  mkRuntime := by
    intro n Γ σ st _ hsupp
    rcases hsupp with ⟨rfl, rfl, rst⟩
    have h_target : st = .declareObj n.τ n.x n.initExpr := by
      simp [ObjectDeclRuntimeCert.targetStmt] at rst
      exact rst
    subst h_target
    cases hinit : n.initExpr with
    | none =>
        exact ObjectDeclRuntimeCert.mkRuntime_none hinit
    | some e =>
        exact ObjectDeclRuntimeCert.mkRuntime_some hinit

namespace ObjectDeclRuntimeCert

@[simp] theorem supportsRuntime_self (c : ObjectDeclRuntimeCert) :
    objectDeclStdFragmentV3.supportsRuntime c c.Γ c.σ c.targetStmt :=
  ⟨rfl, rfl, rfl⟩

def casesOnInit
    {α : Option ValExpr → Sort _}
    (c : ObjectDeclRuntimeCert)
    (h_none : (h : c.initExpr = none) → α none)
    (h_some : ∀ e, (h : c.initExpr = some e) → α (some e)) :
    α c.initExpr :=
  match h : c.initExpr with
  | none => h_none h
  | some e => h_some e h

def toRuntime (c : ObjectDeclRuntimeCert) : RuntimePiecesV3 c.Γ c.σ c.targetStmt :=
  c.casesOnInit (α := fun o => RuntimePiecesV3 c.Γ c.σ (.declareObj c.τ c.x o))
    (fun h => mkRuntime_none h)
    (fun _ h => mkRuntime_some h)

/-- toRuntime の none のケースに関する簡約ルール。 -/
@[simp] theorem toRuntime_none
    (Γ σ x τ ov init ready objTy) :
    let c := ObjectDeclRuntimeCert.mk Γ σ x τ ov (Option.none : Option ValExpr) init ready objTy
    c.toRuntime = mkRuntime_none (n := c) rfl :=
  rfl

/-- toRuntime の some のケースに関する簡約ルール。 -/
@[simp] theorem toRuntime_some
    (Γ σ x τ v e init ready objTy) :
    let c := ObjectDeclRuntimeCert.mk Γ σ x τ (Option.some v) (Option.some e) init ready objTy
    c.toRuntime = mkRuntime_some (n := c) rfl :=
  rfl

@[simp] theorem toRuntime_eq_none
    (c : ObjectDeclRuntimeCert) (h : c.initExpr = none) :
    (h ▸ c.toRuntime : RuntimePiecesV3 c.Γ c.σ (CppStmt.declareObj c.τ c.x none))
    = mkRuntime_none h := by
  rcases c with ⟨Γ, σ, x, τ, ov, (_ | e), init, ready, objTy⟩
  · rfl
  · nomatch h

@[simp] theorem toRuntime_eq_some
    (c : ObjectDeclRuntimeCert) {e : ValExpr} (h : c.initExpr = some e) :
    (h ▸ c.toRuntime : RuntimePiecesV3 c.Γ c.σ (CppStmt.declareObj c.τ c.x (some e)))
    = mkRuntime_some h := by
  rcases c with ⟨Γ, σ, x, τ, ov, (_ | e'), init, ready, objTy⟩
  · nomatch h
  · injection h with h_eq
    subst h_eq
    rfl

theorem targetStmt_eq_none {c : ObjectDeclRuntimeCert} (h : c.initExpr = none) :
    c.targetStmt = .declareObj c.τ c.x none := by
  simp [targetStmt, h]

theorem targetStmt_eq_some {c : ObjectDeclRuntimeCert} {e : ValExpr} (h : c.initExpr = some e) :
    c.targetStmt = .declareObj c.τ c.x (some e) := by
  simp [targetStmt, h]

/-- 統合定理：フレームワークの mkRuntime は、我々の toRuntime と一致する。 -/
theorem objectDeclStdFragmentV3_mkRuntime_eq (c : ObjectDeclRuntimeCert) :
    objectDeclStdFragmentV3.mkRuntime (n := c) trivial ⟨rfl, rfl, rfl⟩ = c.toRuntime := by
  unfold ObjectDeclRuntimeCert.toRuntime ObjectDeclRuntimeCert.casesOnInit
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, init, ready, objTy⟩
  cases initExpr with
  | none =>
      have hov : ov = none := ObjectDeclRuntimeInit.ov_eq_none init
      subst hov
      cases init
      rfl
  | some e =>
      cases init with
      | someInit hty hre hstep hcompat =>
          rfl

@[simp] theorem mkRuntime_self (c : ObjectDeclRuntimeCert) :
    objectDeclStdFragmentV3.mkRuntime (n := c) trivial c.supportsRuntime_self = c.toRuntime := by
  have : c.supportsRuntime_self = ⟨rfl, rfl, rfl⟩ := rfl
  rw [this]
  exact objectDeclStdFragmentV3_mkRuntime_eq c

@[simp] theorem stmtReadyConcrete_eq_target
    (c : ObjectDeclRuntimeCert) :
    StmtReadyConcrete c.Γ c.σ c.targetStmt :=
  c.stmtReadyConcrete


/-- Recover the top type-frame witness needed by
`DeclareObjectReadyRecomputed.declaresObjectWithNext_after`. -/
def topTypeFrameWitness (c : ObjectDeclRuntimeCert) :
    {Γfr : TypeFrame // c.Γ.scopes[0]? = some Γfr} :=
  topTypeFrameWitness_of_currentTypeScopeFresh c.ready.scopeFresh

@[simp] theorem topTypeFrameWitness_spec
    (c : ObjectDeclRuntimeCert) :
    c.Γ.scopes[0]? = some c.topTypeFrameWitness.1 :=
  c.topTypeFrameWitness.2

/-- Canonical post-state determined by the cert. -/
@[simp] def postState (c : ObjectDeclRuntimeCert) : State :=
  declareObjectStateWithNext c.σ c.τ c.x c.ov c.ready.cursor.addr

/-- Cert-level access to the canonical `DeclaresObjectWithNext` witness. -/
@[simp] theorem declaresObjectWithNext
    (c : ObjectDeclRuntimeCert) :
    DeclaresObjectWithNext c.σ c.τ c.x c.ov c.ready.cursor.addr c.postState := by
  rcases c.topTypeFrameWitness with ⟨Γfr, hΓ0⟩
  simpa [ObjectDeclRuntimeCert.postState] using
    (DeclareObjectReadyRecomputed.declaresObjectWithNext_after
      (h := c.ready) hΓ0 c.objTy)

/-- Cert-level access to the existential `DeclaresObject` witness. -/
@[simp] theorem declaresObject
    (c : ObjectDeclRuntimeCert) :
    DeclaresObject c.σ c.τ c.x c.ov c.postState := by
  rcases c.topTypeFrameWitness with ⟨Γfr, hΓ0⟩
  simpa [ObjectDeclRuntimeCert.postState] using
    (DeclareObjectReadyRecomputed.declaresObject_after
      (h := c.ready) hΓ0 c.objTy)

theorem declaresObject_none
    {c : ObjectDeclRuntimeCert}
    (hinit : c.initExpr = none) :
    DeclaresObject c.σ c.τ c.x none c.postState := by
  have hov : c.ov = none := c.ov_eq_none_of_init_none hinit
  simpa [ObjectDeclRuntimeCert.postState, hov] using c.declaresObject

theorem declaresObject_some
    {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) :
    DeclaresObject c.σ c.τ c.x (some (c.storedValueWitness hinit).1) c.postState := by
  have hov : c.ov = some (c.storedValueWitness hinit).1 :=
    c.storedValueWitness_ov hinit
  simpa [ObjectDeclRuntimeCert.postState, hov] using c.declaresObject

/-- Cert-level big-step semantics for the declaration statement itself. -/
def bigStepStmt (c : ObjectDeclRuntimeCert) :
    BigStepStmt c.σ c.targetStmt .normal c.postState := by
  cases hinit : c.initExpr with
  | none =>
      have hdecl : DeclaresObject c.σ c.τ c.x none c.postState :=
        c.declaresObject_none hinit
      simpa [ObjectDeclRuntimeCert.targetStmt, ObjectDeclRuntimeCert.postState, hinit] using
        (BigStepStmt.declareObjNone
          (σ := c.σ) (σ' := c.postState) (τ := c.τ) (x := c.x) hdecl)
  | some e =>
      have hstep : BigStepValue c.σ e (c.storedValueWitness hinit).1 :=
        c.storedValueWitness_bigStep hinit
      have hdecl :
          DeclaresObject c.σ c.τ c.x (some (c.storedValueWitness hinit).1) c.postState :=
        c.declaresObject_some hinit
      simpa [ObjectDeclRuntimeCert.targetStmt, ObjectDeclRuntimeCert.postState, hinit] using
        (BigStepStmt.declareObjSome
          (σ := c.σ) (σ' := c.postState) (τ := c.τ) (x := c.x)
          (e := e) (v := (c.storedValueWitness hinit).1)
          hstep hdecl)

@[simp] theorem bigStepStmt_target
    (c : ObjectDeclRuntimeCert) :
    BigStepStmt c.σ c.targetStmt .normal c.postState :=
  c.bigStepStmt

/-- Canonical post type environment determined by the cert. -/
@[simp] def postTypeEnv (c : ObjectDeclRuntimeCert) : TypeEnv :=
  declareTypeObject c.Γ c.x c.τ

/-- Cert-level preservation of the concrete closure invariant. -/
@[simp] theorem postStateConcrete
    (c : ObjectDeclRuntimeCert) :
    ScopedTypedStateConcrete c.postTypeEnv c.postState := by
  simpa [ObjectDeclRuntimeCert.postTypeEnv] using
    (declares_object_preserves_scoped_typed_state_concrete
      (Γ := c.Γ) (σ := c.σ) (σ' := c.postState)
      (x := c.x) (τ := c.τ) (ov := c.ov)
      c.ready.scopeFresh
      c.ready.ready.concrete
      c.declaresObject)

/-- The cert packages both the normal execution and the post-state invariant. -/
theorem bigStepWithPostConcrete
    (c : ObjectDeclRuntimeCert) :
    BigStepStmt c.σ c.targetStmt .normal c.postState ∧
      ScopedTypedStateConcrete c.postTypeEnv c.postState := by
  exact ⟨c.bigStepStmt, c.postStateConcrete⟩

@[simp] theorem bigStepWithPostConcrete_left
    (c : ObjectDeclRuntimeCert) :
    c.bigStepWithPostConcrete.left =
      (c.bigStepStmt : BigStepStmt c.σ c.targetStmt .normal c.postState) :=
  rfl

@[simp] theorem bigStepWithPostConcrete_right
    (c : ObjectDeclRuntimeCert) :
    c.bigStepWithPostConcrete.right =
      (c.postStateConcrete :
        ScopedTypedStateConcrete c.postTypeEnv c.postState) :=
  rfl

@[simp] theorem bigStepWithPostConcrete_fst
    (c : ObjectDeclRuntimeCert) :
    c.bigStepWithPostConcrete.1 =
      (c.bigStepStmt : BigStepStmt c.σ c.targetStmt .normal c.postState) :=
  rfl

@[simp] theorem bigStepWithPostConcrete_snd
    (c : ObjectDeclRuntimeCert) :
    c.bigStepWithPostConcrete.2 =
      (c.postStateConcrete :
        ScopedTypedStateConcrete c.postTypeEnv c.postState) :=
  rfl


/-- Canonical normal CI typing carried by the cert. -/
@[simp] theorem normalTyping
    (c : ObjectDeclRuntimeCert) :
    HasTypeStmtCI .normalK c.Γ c.targetStmt c.postTypeEnv := by
  cases hinit : c.initExpr with
  | none =>
      simpa [ObjectDeclRuntimeCert.targetStmt, ObjectDeclRuntimeCert.postTypeEnv, hinit] using
        (HasTypeStmtCI.declareObjNone
          (Γ := c.Γ) (τ := c.τ) (x := c.x)
          c.ready.scopeFresh c.objTy)
  | some e =>
      have hty : HasValueType c.Γ e c.τ := c.getHasValueType hinit
      simpa [ObjectDeclRuntimeCert.targetStmt, ObjectDeclRuntimeCert.postTypeEnv, hinit] using
        (HasTypeStmtCI.declareObjSome
          (Γ := c.Γ) (τ := c.τ) (x := c.x) (e := e)
          c.ready.scopeFresh c.objTy hty)

/-- Old coarse typing recovered from the canonical normal CI typing. -/
@[simp] theorem typed0
    (c : ObjectDeclRuntimeCert) :
    WellTypedFrom c.Γ c.targetStmt := by
  exact ⟨c.postTypeEnv, normalCI_to_old_stmt c.normalTyping⟩

/-- Structural boundary extracted from the cert. -/
def bodyStructuralBoundary
    (c : ObjectDeclRuntimeCert) :
    BodyStructuralBoundary c.Γ c.targetStmt := by
  refine
    { wf := ?_
      breakScoped := ?_
      continueScoped := ?_ }
  ·
    cases hinit : c.initExpr with
    | none =>
        simp [ObjectDeclRuntimeCert.targetStmt, hinit, WellFormedStmt]
    | some e =>
        have hty : HasValueType c.Γ e c.τ := c.getHasValueType hinit
        simpa [ObjectDeclRuntimeCert.targetStmt, hinit, WellFormedStmt] using
          (wellFormedValue_of_hasValueType hty)
  ·
    cases hinit : c.initExpr <;>
      simp [ObjectDeclRuntimeCert.targetStmt, hinit, BreakWellScoped, BreakWellScopedAt]
  ·
    cases hinit : c.initExpr <;>
      simp [ObjectDeclRuntimeCert.targetStmt, hinit, ContinueWellScoped, ContinueWellScopedAt]

/-- Canonical normal-out payload for the statement profile. -/
def normalOut
    (c : ObjectDeclRuntimeCert) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK c.Γ c.targetStmt Δ} :=
  ⟨c.postTypeEnv, c.normalTyping⟩

/-- State-free control profile extracted from the cert. -/
def bodyControlProfile
    (c : ObjectDeclRuntimeCert) :
    BodyControlProfile c.Γ c.targetStmt :=
  { summary :=
      { normalOut := some c.normalOut
        returnOut := none } }

/-- Static CI boundary extracted from the cert. -/
def bodyStaticBoundary
    (c : ObjectDeclRuntimeCert) :
    BodyStaticBoundaryCI c.Γ c.targetStmt :=
  { typed0 := c.typed0
    profile := c.bodyControlProfile
    root := .normal c.normalOut
    rootCoherent := BodyRootCoherent.normal rfl }

@[simp] theorem bodyStaticBoundary_profile
    (c : ObjectDeclRuntimeCert) :
    c.bodyStaticBoundary.profile = c.bodyControlProfile :=
  rfl

/-- Object declaration statements cannot produce a top-level return exit. -/
theorem noReturnBigStep
    (c : ObjectDeclRuntimeCert)
    {rv : Option Value} {σ' : State} :
    ¬ BigStepStmt c.σ c.targetStmt (.returnResult rv) σ' := by
  intro hstep
  cases hinit : c.initExpr with
  | none =>
      simp [ObjectDeclRuntimeCert.targetStmt, hinit] at hstep
      cases hstep
  | some e =>
      simp [ObjectDeclRuntimeCert.targetStmt, hinit] at hstep
      cases hstep

/-- Adequacy of the cert-induced control profile. -/
def bodyAdequacyCI
    (c : ObjectDeclRuntimeCert) :
    BodyAdequacyCI c.Γ c.σ c.targetStmt c.bodyControlProfile := by
  refine
    { normalSound := ?_
      returnSound := ?_ }
  ·
    intro σ' hstep
    exact ⟨c.normalOut, rfl⟩
  ·
    intro rv σ' hstep
    exact False.elim (c.noReturnBigStep hstep)

/-- Fully assembled CI closure boundary extracted from the cert. -/
def bodyClosureBoundaryCI
    (c : ObjectDeclRuntimeCert) :
    BodyClosureBoundaryCI c.Γ c.σ c.targetStmt := by
  refine
    { structural := c.bodyStructuralBoundary
      static := c.bodyStaticBoundary
      dynamic := c.bodyDynamicBoundary
      adequacy := ?_ }
  simpa [ObjectDeclRuntimeCert.bodyStaticBoundary] using c.bodyAdequacyCI

/-- Legacy CI wrapper, recovered from the assembled boundary. -/
def bodyReadyCI
    (c : ObjectDeclRuntimeCert) :
    BodyReadyCI c.Γ c.σ c.targetStmt :=
  c.bodyClosureBoundaryCI.toBodyReadyCI

@[simp] theorem bodyReadyCI_safe
    (c : ObjectDeclRuntimeCert) :
    c.bodyReadyCI.dynamic.safe = c.stmtReadyConcrete := by
  simp

@[simp] theorem bodyReadyCI_state
    (c : ObjectDeclRuntimeCert) :
    c.bodyReadyCI.dynamic.state = c.ready.ready.concrete := by
  simp

@[simp] theorem targetStmt_inCoreBigStepFragment
    (c : ObjectDeclRuntimeCert) :
    CoreBigStepFragment c.targetStmt := by
  cases hinit : c.initExpr <;>
    simp [CoreBigStepFragment, InBigStepFragment, ObjectDeclRuntimeCert.targetStmt, hinit]

/-- Erase the object-declaration-specific cert into the common core big-step cert. -/
def toCoreBigStepCert
    (c : ObjectDeclRuntimeCert) :
    CoreBigStepCert :=
  { Γ := c.Γ
    σ := c.σ
    st := c.targetStmt
    fragment := c.targetStmt_inCoreBigStepFragment
    closure := c.bodyClosureBoundaryCI }

@[simp] theorem toCoreBigStepCert_st
    (c : ObjectDeclRuntimeCert) :
    c.toCoreBigStepCert.st = c.targetStmt :=
  rfl

@[simp] theorem toCoreBigStepCert_bodyReadyCI_safe
    (c : ObjectDeclRuntimeCert) :
    c.toCoreBigStepCert.bodyReadyCI.dynamic.safe = c.stmtReadyConcrete := by
  simp [toCoreBigStepCert, bodyClosureBoundaryCI]

@[simp] theorem toCoreBigStepCert_bodyReadyCI_state
    (c : ObjectDeclRuntimeCert) :
    c.toCoreBigStepCert.bodyReadyCI.dynamic.state = c.ready.ready.concrete := by
  simp [toCoreBigStepCert, bodyClosureBoundaryCI]

end ObjectDeclRuntimeCert

end Cpp
