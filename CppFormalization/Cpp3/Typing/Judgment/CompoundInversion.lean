import CppFormalization.Cpp3.Typing.Judgment.PrimitiveInversion

namespace Cpp3
namespace Typing
namespace Judgment

/-!
# CppFormalization.Cpp3.Typing.Judgment.CompoundInversion

Shape-specific inversion helpers for compound statement and block-body typing.

These helpers reconstruct the Micro composition payloads from the public
`StmtTyping` / `BlockTyping` judgments.  They intentionally remain static: no
runtime continuation, replay, opened-body adequacy, or close-scope preservation
is asserted here.

The payloads in `Micro.Composition` are `Prop`-valued structures, so these
inversions return propositional packages using `∃` and `∨` rather than `Σ` and
`Sum`.
-/

namespace StmtTyping

/-- Invert a typed sequence into either its normal-bind payload or its abrupt
short-circuit payload. -/
theorem seqPayload_of_seq
    {k : ControlKind} {Γ Δ : TypeEnv} {s t : CppStmt}
    (h : StmtTyping k Γ (.seq s t) Δ) :
    (∃ Θ : TypeEnv,
      Micro.Composition.NormalBindStatic StmtTyping k Γ Θ Δ s t) ∨
    Micro.Composition.AbruptShortCircuitStatic StmtTyping k Γ Δ s t := by
  cases h with
  | primitive hp =>
      cases hp.formation
  | seqNormal hHead hTail =>
      left
      exact ⟨_, { headNormal := hHead, tail := hTail }⟩
  | seqAbrupt habrupt hHead =>
      right
      exact { abrupt := habrupt, head := hHead }

/-- Invert an `if` typing into its static condition/branch-merge payload. -/
theorem iteStatic_of_ite
    {k : ControlKind} {Γ Δ : TypeEnv} {cond : CppCond} {s t : CppStmt}
    (h : StmtTyping k Γ (.ite cond s t) Δ) :
    ∃ Γc : TypeEnv,
      Micro.Composition.IteStatic StmtTyping k Γ Γc Δ cond s t := by
  cases h with
  | primitive hp =>
      cases hp.formation
  | ite hcond hThen hElse =>
      exact
        ⟨_,
          { condition := hcond
            branches :=
              { thenTyping := hThen
                elseTyping := hElse } }⟩

/-- Invert a normal-channel `while` typing into its static while-normal payload. -/
theorem whileNormalStatic_of_whileNormal
    {Γ : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : StmtTyping .normalK Γ (.whileStmt cond body) Γ) :
    ∃ Γc : TypeEnv,
      Micro.Composition.WhileNormalStatic StmtTyping Γ Γc cond body := by
  cases h with
  | primitive hp =>
      cases hp.formation
  | whileNormal hcond hNormal hBreak hContinue =>
      exact
        ⟨_,
          { condition := hcond
            channels :=
              { normalBody := hNormal
                breakBody := hBreak
                continueBody := hContinue } }⟩

/-- Invert a return-channel `while` typing into its static while-return payload. -/
theorem whileReturnStatic_of_whileReturn
    {Γ Δ : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : StmtTyping .returnK Γ (.whileStmt cond body) Δ) :
    ∃ Γc : TypeEnv,
      Micro.Composition.WhileReturnStatic StmtTyping Γ Γc Δ cond body := by
  cases h with
  | primitive hp =>
      cases hp.formation
  | whileReturn hcond hNormal hBreak hContinue hReturn =>
      exact
        ⟨_,
          { normalPayload :=
              { condition := hcond
                channels :=
                  { normalBody := hNormal
                    breakBody := hBreak
                    continueBody := hContinue } }
            returnChannel :=
              { returnBody := hReturn } }⟩

/-- Invert a block statement typing into its separated scope-entry/opened-body/
scope-exit payload. -/
theorem blockScopeStatic_of_block
    {k : ControlKind} {Γ : TypeEnv} {ss : StmtBlock}
    (h : StmtTyping k Γ (.block ss) Γ) :
    ∃ Γopen : TypeEnv, ∃ Θ : TypeEnv,
      Micro.Composition.BlockScopeStatic BlockTyping k Γ Γopen Θ Γ ss := by
  cases h with
  | primitive hp =>
      cases hp.formation
  | block hEntry hBody hExit =>
      exact
        ⟨_, _,
          { entry := hEntry
            openedBody := { bodyTyping := hBody }
            exit := hExit }⟩

end StmtTyping

namespace BlockTyping

/-- Invert an empty block-body typing. -/
theorem normal_of_nil
    {k : ControlKind} {Γ Δ : TypeEnv}
    (h : BlockTyping k Γ .nil Δ) :
    k = .normalK ∧ Δ = Γ := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Invert a typed block cons into either its normal-cons payload or its abrupt
short-circuit payload. -/
theorem consPayload_of_cons
    {k : ControlKind} {Γ Δ : TypeEnv} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTyping k Γ (.cons head tail) Δ) :
    (∃ Θ : TypeEnv,
      Micro.Composition.BlockConsNormalStatic StmtTyping BlockTyping k Γ Θ Δ head tail) ∨
    Micro.Composition.BlockConsAbruptStatic StmtTyping k Γ Δ head tail := by
  cases h with
  | consNormal hHead hTail =>
      exact Or.inl ⟨_, { headNormal := hHead, tailTyping := hTail }⟩
  | consAbrupt hAbrupt hHead =>
      exact Or.inr { abrupt := hAbrupt, headTyping := hHead }

end BlockTyping

end Judgment
end Typing
end Cpp3
