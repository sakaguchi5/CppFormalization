import CppFormalization.Cpp2.Closure.External.StdFragmentV3
import CppFormalization.Cpp2.Closure.Transitions.Major.ObjectDeclRuntimeBridgeV3

namespace Cpp

/-!
# Closure.External.ObjectDeclStdFragmentV3

Concrete theorem-backed std/runtime fragment for object-declaration statements.

This packages the recomputed-cursor object-declaration runtime builders into
an actual `VerifiedStdFragmentV3` instance, so later ready/glue assembly can
use a non-toy runtime side.
-/

/-- Runtime-side certificate for an object-declaration statement. -/
structure ObjectDeclRuntimeCert where
  Γ : TypeEnv
  σ : State
  x : Ident
  τ : CppType
  ov : Option Value
  initExpr : Option ValExpr
  initStored : ObjectDeclInitStoredValue σ τ initExpr ov
  ready : DeclareObjectReadyRecomputed Γ σ x τ ov
  objTy : ObjectType τ
  hasExprTy :
    match initExpr with
    | none => True
    | some e => HasValueType Γ e τ
  exprReady :
    match initExpr with
    | none => True
    | some e => ExprReadyConcrete Γ σ e τ

/-- 初期化式がある場合、その型が τ であることを抽出する -/
def ObjectDeclRuntimeCert.getHasValueType (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) : HasValueType c.Γ e c.τ := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases h_expr
  exact hasExprTy

/-- 初期化式がある場合、その readiness を抽出する -/
def ObjectDeclRuntimeCert.getExprReady (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) : ExprReadyConcrete c.Γ c.σ e c.τ := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases h_expr
  exact exprReady

/-- 初期化式がある場合、その式が最終的に格納する concrete value を抽出する -/
def ObjectDeclRuntimeCert.getStoredValue (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (h_expr : c.initExpr = some e) :
    ∃ v, c.ov = some v ∧ BigStepValue c.σ e v ∧ ValueCompat v c.τ := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases h_expr
  rcases ObjectDeclInitStoredValue.witness initStored with ⟨v, hov, hstep, hcompat⟩
  exact ⟨v, hov, hstep, hcompat⟩

namespace ObjectDeclRuntimeCert

@[simp] def targetStmt (c : ObjectDeclRuntimeCert) : CppStmt :=
  .declareObj c.τ c.x c.initExpr

@[simp] theorem targetStmt_none
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    {hstore : ObjectDeclInitStoredValue σ τ none ov}
    {h : DeclareObjectReadyRecomputed Γ σ x τ ov}
    {hobj : ObjectType τ} :
    (ObjectDeclRuntimeCert.mk Γ σ x τ ov none hstore h hobj True.intro True.intro).targetStmt =
      .declareObj τ x none := rfl

@[simp] theorem targetStmt_some
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    {e : ValExpr}
    {hstore : ObjectDeclInitStoredValue σ τ (some e) ov}
    {h : DeclareObjectReadyRecomputed Γ σ x τ ov}
    {hobj : ObjectType τ}
    {hty : HasValueType Γ e τ}
    {hre : ExprReadyConcrete Γ σ e τ} :
    (ObjectDeclRuntimeCert.mk Γ σ x τ ov (some e) hstore h hobj hty hre).targetStmt =
      .declareObj τ x (some e) := rfl

@[simp] theorem ov_eq_none_of_init_none
    {c : ObjectDeclRuntimeCert} (hinit : c.initExpr = none) :
    c.ov = none := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases hinit
  exact ObjectDeclInitStoredValue.ov_eq_none initStored

/-- 初期化式がある場合の stored-value witness を subtype として取り出す。 -/
def storedValueWitness (c : ObjectDeclRuntimeCert) {e : ValExpr}
    (hinit : c.initExpr = some e) :
    {v : Value // c.ov = some v ∧ BigStepValue c.σ e v ∧ ValueCompat v c.τ} := by
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases hinit
  exact ObjectDeclInitStoredValue.witness initStored

/-- 初期化式がある場合、ov は必ず some v になる -/
theorem ov_is_some_of_init_some {c : ObjectDeclRuntimeCert} {e : ValExpr}
    (hinit : c.initExpr = some e) : ∃ v, c.ov = some v := by
  let ⟨v, h_ov, _⟩ := c.getStoredValue hinit
  exists v

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
      have hreadyNone : DeclareObjectReadyRecomputed c.Γ c.σ c.x c.τ none :=
        (c.ov_eq_none_of_init_none hinit) ▸ c.ready
      simpa [ObjectDeclRuntimeCert.targetStmt, hinit] using
        DeclareObjectReadyRecomputed.toStmtReadyConcrete_declareObjNone
          hreadyNone c.objTy
  | some e =>
      have hty : HasValueType c.Γ e c.τ := c.getHasValueType hinit
      have hre : ExprReadyConcrete c.Γ c.σ e c.τ := c.getExprReady hinit
      simpa [ObjectDeclRuntimeCert.targetStmt, hinit] using
        DeclareObjectReadyRecomputed.toStmtReadyConcrete_declareObjSome
          (h := c.ready) c.objTy hty hre

def mkRuntime_none {n : ObjectDeclRuntimeCert} (hinit : n.initExpr = none) :
    RuntimePiecesV3 n.Γ n.σ (.declareObj n.τ n.x none) := by
  rcases n with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases hinit
  have hov : ov = none :=
    ObjectDeclInitStoredValue.ov_eq_none_of_none initStored
  subst hov
  exact DeclareObjectReadyRecomputed.runtimePieces_declareObjNone ready objTy

def mkRuntime_some {n : ObjectDeclRuntimeCert} {e : ValExpr} (hinit : n.initExpr = some e) :
    RuntimePiecesV3 n.Γ n.σ (.declareObj n.τ n.x (some e)) := by
  rcases n with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  dsimp at hinit
  subst hinit
  dsimp at hasExprTy exprReady
  exact DeclareObjectReadyRecomputed.runtimePieces_declareObjSome ready objTy hasExprTy exprReady

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

/-- toRuntime の none のケースに関する簡約ルール -/
@[simp] theorem toRuntime_none
    (Γ σ x τ ov initStored ready objTy hasExprTy exprReady) :
    let c := ObjectDeclRuntimeCert.mk Γ σ x τ ov none initStored ready objTy hasExprTy exprReady
    c.toRuntime = mkRuntime_none (n := c) rfl :=
  rfl

/-- toRuntime の some のケースに関する簡約ルール -/
@[simp] theorem toRuntime_some
    (Γ σ x τ ov e initStored ready objTy hasExprTy exprReady) :
    let c := ObjectDeclRuntimeCert.mk Γ σ x τ ov (some e) initStored ready objTy hasExprTy exprReady
    c.toRuntime = mkRuntime_some (n := c) rfl :=
  rfl

@[simp] theorem toRuntime_eq_none
    (c : ObjectDeclRuntimeCert) (h : c.initExpr = none) :
    (h ▸ c.toRuntime : RuntimePiecesV3 c.Γ c.σ (CppStmt.declareObj c.τ c.x none))
    = mkRuntime_none h := by
  rcases c with ⟨Γ, σ, x, τ, ov, (_ | e), initStored, ready, objTy, hasExprTy, exprReady⟩
  · rfl
  · nomatch h

@[simp] theorem toRuntime_eq_some
    (c : ObjectDeclRuntimeCert) {e : ValExpr} (h : c.initExpr = some e) :
    (h ▸ c.toRuntime : RuntimePiecesV3 c.Γ c.σ (CppStmt.declareObj c.τ c.x (some e)))
    = mkRuntime_some h := by
  rcases c with ⟨Γ, σ, x, τ, ov, (_ | e'), initStored, ready, objTy, hasExprTy, exprReady⟩
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

/-- 統合定理：フレームワークの mkRuntime は、我々の toRuntime と一致する -/
theorem objectDeclStdFragmentV3_mkRuntime_eq (c : ObjectDeclRuntimeCert) :
    objectDeclStdFragmentV3.mkRuntime (n := c) trivial ⟨rfl, rfl, rfl⟩ = c.toRuntime := by
  unfold ObjectDeclRuntimeCert.toRuntime ObjectDeclRuntimeCert.casesOnInit
  rcases c with ⟨Γ, σ, x, τ, ov, initExpr, initStored, ready, objTy, hasExprTy, exprReady⟩
  cases initExpr with
  | none =>
      dsimp [ObjectDeclRuntimeCert] at *
      have hov : ov = none := ObjectDeclInitStoredValue.ov_eq_none initStored
      subst hov
      dsimp [ObjectDeclInitStoredValue] at initStored
      cases initStored
      rfl
  | some e =>
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


end ObjectDeclRuntimeCert

end Cpp
