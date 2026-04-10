import CppFormalization.Cpp2.Closure.External.SplitBuilderV3
import CppFormalization.Cpp2.Closure.External.ToyReadyInstanceV3
import CppFormalization.Cpp2.Closure.External.ToyGlueInstanceV3


namespace Cpp

/-!
# Closure.External.ToySplitBuilderV3

Stage 8: first concrete consumer of the split-artifact builder.

Unlike `ToyBuilderV3`, this file does not start from one collapsed certificate family.
Instead it packages the same toy world into two artifact classes:
- a runtime-side artifact carrying the state-indexed ready witness,
- a reflection-side artifact carrying the structural/profile/core package.

The point is not yet to model a fully realistic compiler pipeline, but to verify
that the Stage 7 split builder is inhabited on the first concrete family and
lands on the same official quotient as the earlier hand-written toy routes.
-/

structure ToySplitRuntimeArtifactV3 where
  Γ : TypeEnv
  σ : State
  st : CppStmt
  ready : BodyReadyCI Γ σ st

structure ToySplitReflectionArtifactV3 where
  Γ : TypeEnv
  st : CppStmt
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  core : CoreBigStepFragment st

def ToyReadyCertificate.toSplitRuntimeArtifact
    (c : ToyReadyCertificate) : ToySplitRuntimeArtifactV3 :=
  { Γ := c.Γ, σ := c.σ, st := c.st, ready := c.ready }

def ToyReadyCertificate.toSplitReflectionArtifact
    (c : ToyReadyCertificate) : ToySplitReflectionArtifactV3 :=
  { Γ := c.Γ
    st := c.st
    structural := c.ready.toStructural
    profile := c.ready.toProfile
    core := c.core }

def toySplitMkReflection
    (m : ToySplitReflectionArtifactV3)
    {Γ : TypeEnv} {st : CppStmt}
    (_hgen : st = m.st)
    (hsupp : Γ = m.Γ ∧ st = m.st) :
    ReflectionPiecesV3 Γ st := by
  rcases hsupp with ⟨rfl, rfl⟩
  exact
    { structural := m.structural
      profile := m.profile
      core := m.core }


@[simp] theorem toySplitMkReflection_structural_heq
    (m : ToySplitReflectionArtifactV3)
    {Γ : TypeEnv} {st : CppStmt}
    (hgen : st = m.st)
    (hsupp : Γ = m.Γ ∧ st = m.st) :
    HEq (toySplitMkReflection m hgen hsupp).structural m.structural := by
  cases m with
  | mk mΓ mst mstruct mprof mcore =>
      rcases hsupp with ⟨hΓ, hst⟩
      subst Γ
      subst st
      simp


@[simp] theorem toySplitMkReflection_profile_heq
    (m : ToySplitReflectionArtifactV3)
    {Γ : TypeEnv} {st : CppStmt}
    (hgen : st = m.st)
    (hsupp : Γ = m.Γ ∧ st = m.st) :
    HEq (toySplitMkReflection m hgen hsupp).profile m.profile := by
  cases m with
  | mk mΓ mst mstruct mprof mcore =>
      rcases hsupp with ⟨hΓ, hst⟩
      subst Γ
      subst st
      simp [toySplitMkReflection]

def toySplitFamilyV3 : SplitArtifactFamilyV3 where
  RuntimeName := ToySplitRuntimeArtifactV3
  ReflectionMeta := ToySplitReflectionArtifactV3

  uses := fun _ => True
  supportsRuntime := fun n Γ σ st =>
    Γ = n.Γ ∧ σ = n.σ ∧ st = n.st

  generates := fun m st => st = m.st
  supportsReflection := fun m Γ st =>
    Γ = m.Γ ∧ st = m.st

  mkRuntime := by
    intro n Γ σ st _ hsupp
    rcases hsupp with ⟨rfl, rfl, rfl⟩
    exact { dynamic := n.ready.toDynamic }

  mkReflection := by
    intro m Γ st hgen hsupp
    exact toySplitMkReflection m hgen hsupp

  compatible := fun n m Γ σ st =>
    n.Γ = Γ ∧ n.σ = σ ∧ n.st = st ∧
    m.Γ = Γ ∧ m.st = st ∧
    -- ∃ を使わず、推移律から導かれるはずの直接の等式を書く
    HEq n.ready.toStructural m.structural ∧
    HEq n.ready.toProfile m.profile

  mkReady := by
    intro n m Γ σ st _ _ _ _ hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, _, _, _, _⟩
    exact n.ready

  dynamic_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hcompat with ⟨rfl, rfl, rfl, _, _, _, _⟩
    rcases hsuppRun with ⟨_, _, _⟩
    rfl

  structural_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hsuppRun with ⟨rfl, rfl, rfl⟩
    rcases hsuppRefl with ⟨_, _⟩
    rcases hcompat with ⟨_, _, _, _, _, hstruct, _⟩
    simp

  profile_eq := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    rcases hsuppRun with ⟨rfl, rfl, rfl⟩
    rcases hcompat with ⟨_, _, _, _, _, _, hprof⟩
    have hmk :
        HEq (toySplitMkReflection m hgen hsuppRefl).profile m.profile :=
      toySplitMkReflection_profile_heq m hgen hsuppRefl
    change n.ready.toProfile =
      (toySplitMkReflection m hgen hsuppRefl).profile
    exact eq_of_heq (HEq.trans hprof (HEq.symm hmk))

theorem toySplit_uses (c : ToyReadyCertificate) :
    toySplitFamilyV3.uses c.toSplitRuntimeArtifact := by
  trivial

theorem toySplit_supportsRuntime (c : ToyReadyCertificate) :
    toySplitFamilyV3.supportsRuntime
      c.toSplitRuntimeArtifact c.Γ c.σ c.st := by
  exact ⟨rfl, rfl, rfl⟩

theorem toySplit_generates (c : ToyReadyCertificate) :
    toySplitFamilyV3.generates c.toSplitReflectionArtifact c.st := by
  rfl

theorem toySplit_supportsReflection (c : ToyReadyCertificate) :
    toySplitFamilyV3.supportsReflection
      c.toSplitReflectionArtifact c.Γ c.st := by
  exact ⟨rfl, rfl⟩

theorem toySplit_compatible (c : ToyReadyCertificate) :
    toySplitFamilyV3.compatible
      c.toSplitRuntimeArtifact c.toSplitReflectionArtifact c.Γ c.σ c.st := by
  -- 定義を展開して型を露わにする
  simp [toySplitFamilyV3, ToyReadyCertificate.toSplitRuntimeArtifact, ToyReadyCertificate.toSplitReflectionArtifact]

def toySplitReadyExternalPiecesV3
    (c : ToyReadyCertificate) : ExternalPiecesV3 c.Γ c.σ c.st :=
  toySplitFamilyV3.readyExternalPieces
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)

noncomputable def toySplitGlueExternalPiecesV3
    (c : ToyReadyCertificate) : ExternalPiecesV3 c.Γ c.σ c.st :=
  toySplitFamilyV3.glueExternalPieces
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)

theorem toySplit_ready_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  exact toySplitFamilyV3.stmt_closure_from_ready
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)

theorem toySplit_glue_certificate_closure
    (c : ToyReadyCertificate) :
    BigStepStmtTerminates c.σ c.st ∨ BigStepStmtDiv c.σ c.st := by
  exact toySplitFamilyV3.stmt_closure_from_glue
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)

theorem toySplit_ready_vs_glue_packageCoherent
    (c : ToyReadyCertificate) :
    PackageCoherentV3
      (toySplitReadyExternalPiecesV3 c).toVisiblePieces
      (toySplitGlueExternalPiecesV3 c).toVisiblePieces := by
  exact toySplitFamilyV3.ready_vs_glue_packageCoherent
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)

theorem toySplit_glue_readyInduced_boundaryCoherent
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 toySplitFamilyV3.toGlue)
        (toySplit_uses c)
        (toySplit_supportsRuntime c)
        (toySplit_generates c)
        (toySplit_supportsReflection c)
        (toySplit_compatible c))
      (toySplitGlueExternalPiecesV3 c) := by
  exact toySplitFamilyV3.glue_readyInduced_boundaryCoherent
    (toySplit_uses c)
    (toySplit_supportsRuntime c)
    (toySplit_generates c)
    (toySplit_supportsReflection c)
    (toySplit_compatible c)


/--
`mkReady` の自己入力を明示的に `c` の index
(`n, m, Γ, σ, st`) に固定したうえで、
`compatible` を分解し、返り値が定義的に `c.ready` に簡約されることを示す。
-/
theorem toySplitFamilyV3_mkReady_eq (c : ToyReadyCertificate) :
    toySplitFamilyV3.mkReady
      (toySplit_uses c)
      (toySplit_supportsRuntime c)
      (toySplit_generates c)
      (toySplit_supportsReflection c)
      (toySplit_compatible c) = c.ready := by
  change
    toySplitFamilyV3.mkReady
      (n := c.toSplitRuntimeArtifact)
      (m := c.toSplitReflectionArtifact)
      (Γ := c.Γ) (σ := c.σ) (st := c.st)
      (toySplit_uses c)
      (toySplit_supportsRuntime c)
      (toySplit_generates c)
      (toySplit_supportsReflection c)
      (toySplit_compatible c)
      = c.ready
  unfold toySplitFamilyV3
  rcases toySplit_compatible c with ⟨_, _, _, _, _, _, _⟩
  rfl

/-- Split Family の readyExternalPieces が提供する境界の正当性 -/
theorem toySplitReadyExternalPiecesV3_boundary_eq
    (c : ToyReadyCertificate) :
    (toySplitReadyExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  -- 1. 外部定義の展開
  simp [toySplitReadyExternalPiecesV3]

  -- 2. 一般論 (SplitArtifactFamilyV3.readyExternalPieces_boundary) の適用
  rw [toySplitFamilyV3.readyExternalPieces_boundary
        (toySplit_uses c)
        (toySplit_supportsRuntime c)
        (toySplit_generates c)
        (toySplit_supportsReflection c)
        (toySplit_compatible c)]

  -- 3. 橋渡し補題を適用して mkReady を c.ready に書き換える
  rw [toySplitFamilyV3_mkReady_eq c]

/-- 元の toyExternalPiecesV3 が提供する境界の正当性 -/
theorem toyExternalPiecesV3_boundary_eq_ready
    (c : ToyReadyCertificate) :
    (toyExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  -- 既存の toyExternalPiecesV3_boundary を利用
  exact toyExternalPiecesV3_boundary c

/--
  Split版の ReadyPieces と、直接構築した ExternalPieces の境界は一致する
-/
theorem toySplit_builder_ready_boundary_eq_handwritten
    (c : ToyReadyCertificate) :
  (toySplitReadyExternalPiecesV3 c).toBodyBoundary =
    (toyExternalPiecesV3 c).toBodyBoundary := by
  rw [toySplitReadyExternalPiecesV3_boundary_eq]
  rw [toyExternalPiecesV3_boundary_eq_ready]

/-- 補題A: Split版の Glue と Ready の境界は（コヒーレンスにより）一致する -/
theorem toySplit_glue_boundary_eq_ready_boundary
    (c : ToyReadyCertificate) :
    (toySplitGlueExternalPiecesV3 c).toBodyBoundary =
    (toySplitReadyExternalPiecesV3 c).toBodyBoundary := by
  -- コヒーレンスを取り出す
  let h := toySplit_glue_readyInduced_boundaryCoherent c
  -- BoundaryCoherentV3 は定義上、境界の一致を意味するため、対称性を取って適用
  symm
  exact h

/-- 補題B: Split版の GlueExternalPieces が提供する境界の正当性 -/
theorem toySplitGlueExternalPiecesV3_boundary_eq
    (c : ToyReadyCertificate) :
    (toySplitGlueExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  rw [toySplit_glue_boundary_eq_ready_boundary]
  rw [toySplitReadyExternalPiecesV3_boundary_eq]

/-- 補題C: 直接構築版 (Handwritten) の GlueExternalPieces が提供する境界の正当性 -/
theorem toyGlueExternalPiecesV3_boundary_eq_ready
    (c : ToyReadyCertificate) :
    (toyGlueExternalPiecesV3 c).toBodyBoundary = c.ready.toClosureBoundary := by
  exact toyGlueExternalPiecesV3_boundary c

/--
  Split版の GluePieces と、直接構築した GluePieces の境界は一致する
-/
theorem toySplit_builder_glue_boundary_eq_handwritten
    (c : ToyReadyCertificate) :
    (toySplitGlueExternalPiecesV3 c).toBodyBoundary =
      (toyGlueExternalPiecesV3 c).toBodyBoundary := by
  rw [toySplitGlueExternalPiecesV3_boundary_eq]
  rw [toyGlueExternalPiecesV3_boundary_eq_ready]

theorem toySplit_builder_ready_boundaryCoherent_handwritten
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (toySplitReadyExternalPiecesV3 c)
      (toyExternalPiecesV3 c) := by
  exact toySplit_builder_ready_boundary_eq_handwritten c

theorem toySplit_builder_glue_boundaryCoherent_handwritten
    (c : ToyReadyCertificate) :
    BoundaryCoherentV3
      (toySplitGlueExternalPiecesV3 c)
      (toyGlueExternalPiecesV3 c) := by
  exact toySplit_builder_glue_boundary_eq_handwritten c

end Cpp
