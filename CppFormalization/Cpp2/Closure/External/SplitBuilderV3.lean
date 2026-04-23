import CppFormalization.Cpp2.Closure.External.ReadyFromGlueV3
import CppFormalization.Cpp2.Closure.External.AssembleLemmasV3

namespace Cpp

/-!
# Closure.External.SplitBuilderV3

Stage 7 preparatory split-artifact builder.

`BuilderV3` packages a single target-indexed certificate family that already carries
both a ready witness and a core witness.  That is the right abstraction for toy
families and for the legacy lift, but it is still more collapsed than a future
"real" external artifact family is likely to be.

This file introduces a more split builder input:
- one runtime-side artifact type,
- one reflection-side artifact type,
- one compatibility relation tying them to a common target,
- and one integrated ready witness for each compatible pair.

From that data we reconstruct the same V3 routes:
- the runtime/std fragment,
- the reflection fragment,
- the high-level ready assembly,
- the low-level glue assembly,
- and the basic route-level corollaries.

This is the natural next scaffold before introducing a heavier compiler-like
artifact family whose runtime and reflection evidence are not stored in a single
certificate object.
-/

structure SplitArtifactFamilyV3 where
  RuntimeName : Type
  ReflectionMeta : Type

  uses : RuntimeName → Prop
  supportsRuntime : RuntimeName → TypeEnv → State → CppStmt → Prop

  generates : ReflectionMeta → CppStmt → Prop
  supportsReflection : ReflectionMeta → TypeEnv → CppStmt → Prop

  mkRuntime :
    ∀ {n : RuntimeName} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n →
      supportsRuntime n Γ σ st →
      RuntimePiecesV3 Γ σ st

  mkReflection :
    ∀ {m : ReflectionMeta} {Γ : TypeEnv} {st : CppStmt},
      generates m st →
      supportsReflection m Γ st →
      ReflectionPiecesV3 Γ st

  compatible :
    RuntimeName → ReflectionMeta → TypeEnv → State → CppStmt → Prop

  mkReady :
    ∀ {n : RuntimeName} {m : ReflectionMeta} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n →
      supportsRuntime n Γ σ st →
      generates m st →
      supportsReflection m Γ st →
      compatible n m Γ σ st →
      BodyReadyCI Γ σ st

  dynamic_eq :
    ∀ {n : RuntimeName} {m : ReflectionMeta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : uses n)
      (hsuppRun : supportsRuntime n Γ σ st)
      (hgen : generates m st)
      (hsuppRefl : supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).toDynamic =
        (mkRuntime huse hsuppRun).dynamic

  structural_eq :
    ∀ {n : RuntimeName} {m : ReflectionMeta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : uses n)
      (hsuppRun : supportsRuntime n Γ σ st)
      (hgen : generates m st)
      (hsuppRefl : supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).toStructural =
        (mkReflection hgen hsuppRefl).structural

  static_eq :
    ∀ {n : RuntimeName} {m : ReflectionMeta} {Γ : TypeEnv} {σ : State} {st : CppStmt}
      (huse : uses n)
      (hsuppRun : supportsRuntime n Γ σ st)
      (hgen : generates m st)
      (hsuppRefl : supportsReflection m Γ st)
      (hcompat : compatible n m Γ σ st),
      (mkReady huse hsuppRun hgen hsuppRefl hcompat).static =
        (mkReflection hgen hsuppRefl).static

namespace SplitArtifactFamilyV3

def toStdFragment (A : SplitArtifactFamilyV3) : VerifiedStdFragmentV3 where
  Name := A.RuntimeName
  uses := A.uses
  supportsRuntime := A.supportsRuntime
  mkRuntime := A.mkRuntime

def toReflectionFragment (A : SplitArtifactFamilyV3) : VerifiedReflectionFragmentV3 where
  Meta := A.ReflectionMeta
  generates := A.generates
  supportsReflection := A.supportsReflection
  mkReflection := A.mkReflection

def toReadyAssembly (A : SplitArtifactFamilyV3) :
    VerifiedExternalReadyAssemblyV3 A.toStdFragment A.toReflectionFragment where
  compatible := A.compatible
  mkReady := A.mkReady
  dynamic_eq := A.dynamic_eq
  structural_eq := A.structural_eq
  static_eq := A.static_eq



def mkAdequacy_from_compatible
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    BodyAdequacyCI Γ σ st ((A.mkReflection hgen hsuppRefl).static.profile) :=
  let hready := A.mkReady huse hsuppRun hgen hsuppRefl hcompat
  let hstatic := A.static_eq huse hsuppRun hgen hsuppRefl hcompat
  match (A.mkReflection hgen hsuppRefl).static, hstatic with
  | _, rfl => hready.toAdequacy

def toGlue (A : SplitArtifactFamilyV3) :
    VerifiedExternalGlueV3 A.toStdFragment A.toReflectionFragment where
  compatible := A.compatible
  mkAdequacy := by
    intro n m Γ σ st huse hsuppRun hgen hsuppRefl hcompat
    exact mkAdequacy_from_compatible A huse hsuppRun hgen hsuppRefl hcompat

def readyExternalPieces
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st :=
  externalPieces_of_ready_v3 A.toReadyAssembly
    huse hsuppRun hgen hsuppRefl hcompat

noncomputable def glueExternalPieces
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    ExternalPiecesV3 Γ σ st :=
  assembleExternalPiecesV3 A.toGlue
    huse hsuppRun hgen hsuppRefl hcompat

theorem readyExternalPieces_boundary
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toBodyBoundary =
      (A.mkReady huse hsuppRun hgen hsuppRefl hcompat).toClosureBoundary := by
  simpa [readyExternalPieces] using
    (externalPieces_of_ready_v3_boundary
      (A := A.toReadyAssembly)
      (huse := huse)
      (hsuppRun := hsuppRun)
      (hgen := hgen)
      (hsuppRefl := hsuppRefl)
      (hcompat := hcompat))

theorem readyExternalPieces_packageCoherent
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    PackageCoherentV3
      (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (canonicalVisiblePiecesV3 (F := A.toStdFragment) (R := A.toReflectionFragment) huse hsuppRun hgen hsuppRefl) := by
  simpa [readyExternalPieces] using
    (externalPieces_of_ready_v3_packageCoherent
      (A := A.toReadyAssembly)
      (huse := huse)
      (hsuppRun := hsuppRun)
      (hgen := hgen)
      (hsuppRefl := hsuppRefl)
      (hcompat := hcompat))

theorem glueExternalPieces_packageCoherent
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    PackageCoherentV3
      (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (canonicalVisiblePiecesV3 (F := A.toStdFragment) (R := A.toReflectionFragment) huse hsuppRun hgen hsuppRefl) := by
  simpa [glueExternalPieces] using
    (assembleExternalPiecesV3_packageCoherent
      (G := A.toGlue)
      (huse := huse)
      (hsuppRun := hsuppRun)
      (hgen := hgen)
      (hsuppRefl := hsuppRefl)
      (hcompat := hcompat))

theorem ready_vs_glue_packageCoherent
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    PackageCoherentV3
      (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (A.glueExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces := by
  change
    (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces =
      (A.glueExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
  calc
    (A.readyExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces =
        canonicalVisiblePiecesV3 huse hsuppRun hgen hsuppRefl := by
      exact A.readyExternalPieces_packageCoherent huse hsuppRun hgen hsuppRefl hcompat
    _ =
        (A.glueExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces := by
      symm
      exact A.glueExternalPieces_packageCoherent huse hsuppRun hgen hsuppRefl hcompat

theorem glue_readyInduced_packageCoherent
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    PackageCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 A.toGlue)
        huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces
      (A.glueExternalPieces huse hsuppRun hgen hsuppRefl hcompat).toVisiblePieces := by
  simpa [glueExternalPieces] using
    (externalPieces_of_ready_from_glue_v3_packageCoherent
      (G := A.toGlue)
      (huse := huse)
      (hsuppRun := hsuppRun)
      (hgen := hgen)
      (hsuppRefl := hsuppRefl)
      (hcompat := hcompat))

theorem glue_readyInduced_boundaryCoherent
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : A.uses n)
    (hsuppRun : A.supportsRuntime n Γ σ st)
    (hgen : A.generates m st)
    (hsuppRefl : A.supportsReflection m Γ st)
    (hcompat : A.compatible n m Γ σ st) :
    BoundaryCoherentV3
      (externalPieces_of_ready_v3
        (readyAssembly_of_glue_v3 A.toGlue)
        huse hsuppRun hgen hsuppRefl hcompat)
      (A.glueExternalPieces huse hsuppRun hgen hsuppRefl hcompat) := by
  simpa [glueExternalPieces] using
    (externalPieces_of_ready_from_glue_v3_boundaryCoherent
      (G := A.toGlue)
      (huse := huse)
      (hsuppRun := hsuppRun)
      (hgen := hgen)
      (hsuppRefl := hsuppRefl)
      (hcompat := hcompat))

theorem stmt_closure_from_ready
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    A.uses n →
    A.supportsRuntime n Γ σ st →
    A.generates m st →
    A.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_closure_theorem_from_ready_v3
    A.toReadyAssembly
    huse hsuppRun hgen hsuppRefl hcompat

theorem function_body_closure_from_ready
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    A.uses n →
    A.supportsRuntime n Γ σ st →
    A.generates m st →
    A.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_function_body_closure_from_ready_v3
    A.toReadyAssembly
    huse hsuppRun hgen hsuppRefl hcompat

theorem stmt_closure_from_glue
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    A.uses n →
    A.supportsRuntime n Γ σ st →
    A.generates m st →
    A.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_closure_theorem_v3_via_ready
    A.toGlue
    huse hsuppRun hgen hsuppRefl hcompat

theorem function_body_closure_from_glue
    (A : SplitArtifactFamilyV3)
    {n : A.RuntimeName} {m : A.ReflectionMeta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    A.uses n →
    A.supportsRuntime n Γ σ st →
    A.generates m st →
    A.supportsReflection m Γ st →
    A.compatible n m Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro huse hsuppRun hgen hsuppRefl hcompat
  exact reflective_std_function_body_closure_v3_via_ready
    A.toGlue
    huse hsuppRun hgen hsuppRefl hcompat

end SplitArtifactFamilyV3

end Cpp
