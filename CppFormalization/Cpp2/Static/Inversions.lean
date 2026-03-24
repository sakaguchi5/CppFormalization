import CppFormalization.Cpp2.Static.Assumptions

/-!
Structural inversion lemmas.
-/

namespace Cpp

theorem wf_seq_inv_left {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt s := by
  intro h
  exact h.1

theorem wf_seq_inv_right {s t : CppStmt} :
    WellFormedStmt (.seq s t) → WellFormedStmt t := by
  intro h
  exact h.2

theorem wf_ite_inv_cond {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedValue c := by
  intro h
  exact h.1

theorem wf_ite_inv_then {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt s := by
  intro h
  exact h.2.1

theorem wf_ite_inv_else {c : ValExpr} {s t : CppStmt} :
    WellFormedStmt (.ite c s t) → WellFormedStmt t := by
  intro h
  exact h.2.2

theorem wf_while_inv_body {c : ValExpr} {body : CppStmt} :
    WellFormedStmt (.whileStmt c body) → WellFormedStmt body := by
  intro h
  exact h.2

/-- ブロック内の要素に対する WellFormedStmt の逆転定理 -/
private theorem wf_block_mem
    {ss : StmtBlock} {s : CppStmt} :
    WellFormedBlock ss → StmtBlock.Mem s ss → WellFormedStmt s :=
  match ss with
  | .nil =>
      -- Mem s .nil は False なので、矛盾から証明
      fun _ hmem => False.elim hmem
  | .cons _t _ts =>
      -- h: WellFormedStmt t ∧ WellFormedBlock ts
      -- hmem: s = t ∨ Mem s ts
      fun h hmem =>
        match hmem with
        | Or.inl (heq : s = _t) =>
            -- s = t なので、h の左側 (WellFormedStmt t) が答え
            heq.symm ▸ h.left
        | Or.inr (hmemTail : StmtBlock.Mem s _ts) =>
            -- s が後半にあるので、再帰的に証明
            wf_block_mem h.right hmemTail

theorem wf_block_inv {ss : StmtBlock} {s : CppStmt} :
    WellFormedStmt (.block ss) → StmtBlock.Mem s ss → WellFormedStmt s := by
  intro h hs
  exact wf_block_mem h hs

theorem typed_seq_inv
    {Γ Δ : TypeEnv} {s t : CppStmt} :
    HasTypeStmt Γ (.seq s t) Δ → ∃ Γ₁, HasTypeStmt Γ s Γ₁ ∧ HasTypeStmt Γ₁ t Δ := by
  intro h
  cases h with
  | seq hs ht => exact ⟨_, hs, ht⟩

theorem typed_ite_inv_cond
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasValueType Γ c (.base .bool) := by
  intro h
  cases h with
  | ite hc _ _ => exact hc

theorem typed_ite_inv_then
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasTypeStmt Γ s Δ := by
  intro h
  cases h with
  | ite _ hs _ => exact hs

theorem typed_ite_inv_else
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmt Γ (.ite c s t) Δ → HasTypeStmt Γ t Δ := by
  intro h
  cases h with
  | ite _ _ ht => exact ht

theorem typed_while_inv_cond
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) Γ → HasValueType Γ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc _ => exact hc

theorem typed_while_inv_body
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmt Γ (.whileStmt c body) Γ → HasTypeStmt Γ body Γ := by
  intro h
  cases h with
  | whileStmt _ hb => exact hb

private theorem typed_block_mem
    {Γ Δ : TypeEnv} {ss : StmtBlock} {s : CppStmt} :
    HasTypeBlock Γ ss Δ → StmtBlock.Mem s ss → ∃ Γ₁ Γ₂, HasTypeStmt Γ₁ s Γ₂
  | .nil, hmem => False.elim hmem
  | .cons hs htail, hmem =>
      match hmem with
      | Or.inl heq =>
          heq.symm ▸ ⟨_, _, hs⟩
      | Or.inr hmemTail =>
          typed_block_mem htail hmemTail

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
