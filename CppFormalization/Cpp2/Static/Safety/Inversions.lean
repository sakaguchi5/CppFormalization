import CppFormalization.Cpp2.Static.Pure.Inversions
import CppFormalization.Cpp2.Static.Safety.Assumptions

namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Safety.Inversions

Safety-level inversion facts.

This file contains inversion facts for `NoUninit*`, `NoInvalidRef*`, and
`IdealAssumptions`.  Pure well-formedness and typing inversions live in
`Static.Pure.Inversions`.
-/

theorem no_uninit_seq_inv_left {σ : State} {s t : CppStmt} :
    NoUninitStmt σ (.seq s t) → NoUninitStmt σ s := by
  intro h
  exact h.1

theorem no_uninit_seq_inv_right {σ : State} {s t : CppStmt} :
    NoUninitStmt σ (.seq s t) → NoUninitStmt σ t := by
  intro h
  exact h.2

theorem no_invalid_ref_seq_inv_left {σ : State} {s t : CppStmt} :
    NoInvalidRefStmt σ (.seq s t) → NoInvalidRefStmt σ s := by
  intro h
  exact h.1

theorem no_invalid_ref_seq_inv_right {σ : State} {s t : CppStmt} :
    NoInvalidRefStmt σ (.seq s t) → NoInvalidRefStmt σ t := by
  intro h
  exact h.2

theorem ideal_assumptions_inv_wf {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → WellFormedStmt st := by
  intro h
  exact h.1

theorem ideal_assumptions_inv_typed {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → WellTypedFrom Γ st := by
  intro h
  exact h.2.1

theorem ideal_assumptions_inv_typed_state {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → TypedState Γ σ := by
  intro h
  exact h.2.2.1

theorem ideal_assumptions_inv_no_uninit {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → NoUninitStmt σ st := by
  intro h
  exact h.2.2.2.1

theorem ideal_assumptions_inv_no_invalid_ref {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → NoInvalidRefStmt σ st := by
  intro h
  exact h.2.2.2.2.1

theorem ideal_assumptions_inv_break_scoped {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → BreakWellScoped st := by
  intro h
  exact h.2.2.2.2.2.1

theorem ideal_assumptions_inv_continue_scoped {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    IdealAssumptions Γ σ st → ContinueWellScoped st := by
  intro h
  exact h.2.2.2.2.2.2

end Cpp
