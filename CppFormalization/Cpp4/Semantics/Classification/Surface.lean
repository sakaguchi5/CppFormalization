import CppFormalization.Cpp4.Semantics.Classification.Function
import CppFormalization.Cpp4.Semantics.Surface.ExpandSoundness
import CppFormalization.Cpp4.Semantics.Divergence.Surface

/-!
# CppFormalization.Cpp4.Semantics.Classification.Surface

Surface finite/divergent classification via expansion.
-/

namespace Cpp4

namespace SurfaceClassification

/-- Classification of a surface statement via its expanded ControlPlan. -/
def StmtClassification (χ : KernelContext) (σ : State) (s : CppStmt) : Type :=
  PlanClassification χ σ (expandStmt s)

/-- Classification of a surface block via its expanded PlanBlock. -/
def BlockClassification (χ : KernelContext) (σ : State) (b : StmtBlock) : Type :=
  Cpp4.BlockClassification χ σ (expandBlock b)

/-- A finite surface statement gives a surface classification. -/
def stmtFinite {χ : KernelContext} {σ σ' : State} {s : CppStmt} {r : CtrlResult}
    (h : SurfaceSemantics.BigStepStmt χ σ s r σ') : StmtClassification χ σ s :=
  PlanClassification.finite h

/-- A divergent surface statement gives a surface classification. -/
def stmtDiverges {χ : KernelContext} {σ : State} {s : CppStmt}
    (h : SurfaceDivergence.DivergesStmt χ σ s) : StmtClassification χ σ s :=
  PlanClassification.diverges h

end SurfaceClassification

end Cpp4
