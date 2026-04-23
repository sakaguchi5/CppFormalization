import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI

namespace Cpp

namespace LoopBodyControlProfile

@[simp] theorem normalTyping
    {Γ : TypeEnv} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body) :
    HasTypeStmtCI .normalK Γ body Γ := by
  rcases P.normalClosed with ⟨h, _⟩
  exact h

@[simp] theorem breakTyping
    {Γ : TypeEnv} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body) :
    HasTypeStmtCI .breakK Γ body Γ := by
  rcases P.breakClosed with ⟨h, _⟩
  exact h

@[simp] theorem continueTyping
    {Γ : TypeEnv} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body) :
    HasTypeStmtCI .continueK Γ body Γ := by
  rcases P.continueClosed with ⟨h, _⟩
  exact h

/-- loop body の old normal typing を取り出す。 -/
def oldNormalTyping
    {Γ : TypeEnv} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body) :
    HasTypeStmt Γ body Γ :=
  normalCI_to_old_stmt P.normalTyping

/-- loop body 自体の old coarse typing. -/
def typed0
    {Γ : TypeEnv} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body) :
    WellTypedFrom Γ body :=
  ⟨Γ, P.oldNormalTyping⟩

/-- enclosing `while` の normal typing を作る。 -/
def whileNormalTyping
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  HasTypeStmtCI.while_normal hc P.normalTyping P.breakTyping P.continueTyping

/-- `return` channel があるとき、enclosing `while` の return typing を作る。 -/
def whileReturnTyping
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} {Δ : TypeEnv}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool))
    (hR : HasTypeStmtCI .returnK Γ body Δ) :
    HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ :=
  HasTypeStmtCI.while_return hc P.normalTyping P.breakTyping P.continueTyping hR

/-- `while` normal side の summary slot. -/
def whileNormalOut
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ} :=
  ⟨Γ, P.whileNormalTyping hc⟩

/-- `while` return side の summary slot. -/
def whileReturnOut?
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.whileStmt c body) Δ} :=
  match P.summary.returnOut with
  | none => none
  | some out => some ⟨out.1, P.whileReturnTyping hc out.2⟩

/-- loop-body profile から enclosing `while` の 2-channel summary を組む。 -/
def toWhileSummary
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    StmtBodySummary Γ (.whileStmt c body) :=
  { normalOut := some (P.whileNormalOut hc)
    returnOut := P.whileReturnOut? hc }

/-- loop-body profile から enclosing `while` の top-level 2-channel profile を組む。 -/
def toWhileProfile
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    BodyControlProfile Γ (.whileStmt c body) :=
  { summary := P.toWhileSummary hc }

/-- `while` 自身の old coarse typing. -/
def whileTyped0
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (P : LoopBodyControlProfile Γ body)
    (hc : HasValueType Γ c (.base .bool)) :
    WellTypedFrom Γ (.whileStmt c body) :=
  ⟨Γ, normalCI_to_old_stmt (P.whileNormalTyping hc)⟩

end LoopBodyControlProfile

namespace LoopBodyStructuralBoundary

@[simp] theorem toWhileBreakScoped
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyStructuralBoundary Γ body) :
    BreakWellScoped (.whileStmt c body) := by
  simpa [BreakWellScoped, BreakWellScopedInLoop]
    using h.breakScoped

@[simp] theorem toWhileContinueScoped
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyStructuralBoundary Γ body) :
    ContinueWellScoped (.whileStmt c body) := by
  simpa [ContinueWellScoped, ContinueWellScopedInLoop]
    using h.continueScoped

/-- loop-body structural boundary から enclosing `while` の structural layer を組む。 -/
def toWhileStructural
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyStructuralBoundary Γ body)
    (hwfCond : WellFormedValue c):
    BodyStructuralBoundary Γ (.whileStmt c body) :=
  { wf := by
      exact And.intro hwfCond h.wf
    breakScoped := h.toWhileBreakScoped
    continueScoped := h.toWhileContinueScoped }

end LoopBodyStructuralBoundary

namespace LoopBodyBoundaryCI

def toWhileProfile
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyBoundaryCI Γ σ body)
    (hc : HasValueType Γ c (.base .bool)) :
    BodyControlProfile Γ (.whileStmt c body) :=
  h.profile.toWhileProfile hc

def toWhileEntry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyBoundaryCI Γ σ body)
    (hc : HasValueType Γ c (.base .bool)) :
    BodyEntryWitness Γ (.whileStmt c body) :=
  .normal (h.profile.whileNormalOut hc)

def toWhileStructural
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : LoopBodyBoundaryCI Γ σ body)
    (hwfCond : WellFormedValue c) :
    BodyStructuralBoundary Γ (.whileStmt c body) :=
  h.structural.toWhileStructural hwfCond

end LoopBodyBoundaryCI

end Cpp
