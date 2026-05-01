import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryLite
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfileLite
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyBoundaryLiteCompatibility

lite boundary から flat CI boundary への forgetful compatibility.

三分法:
1. 構成データ層 (`def`)
   - lite profile を flat summary へ潰す関数群
2. 観測命題層 (`theorem`)
   - lite adequacy から flat soundness を取り出す theorem 群
3. 組立層 (`def`)
   - `BodyAdequacyCI` / `BodyReadyCI` / `BodyClosureBoundaryCI` を組み立てる

重要:
- これは `lite -> CI` の忘却であり、`CI -> lite` の再構成ではない。
- `typed0` は `safe : StmtReadyConcrete` からは回復しない。
  その橋は一般には偽だからである。
- 代わりに `typed0` は recursive lite profile から回復する。
-/


/-! ## 1. 構成データ層: recursive lite profiles -> flat summaries -/

mutual

def stmtNormalOut_of_profileLite
    {Γ : TypeEnv} {st : CppStmt} :
    StmtBodyProfileLite Γ st →
    Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  | .leaf S =>
      S.normalOut
  | .seq hN _ P₂ =>
      match stmtNormalOut_of_profileLite P₂ with
      | some out =>
          some ⟨out.1, HasTypeStmtCI.seq_normal hN out.2⟩
      | none =>
          none
  | .block P =>
      match blockNormalOut_of_profileLite P with
      | some out =>
          some ⟨Γ, HasTypeStmtCI.block out.2⟩
      | none =>
          none

def stmtReturnOut_of_profileLite
    {Γ : TypeEnv} {st : CppStmt} :
    StmtBodyProfileLite Γ st →
    Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}
  | .leaf S =>
      S.returnOut
  | .seq hN P₁ P₂ =>
      match stmtReturnOut_of_profileLite P₁ with
      | some outS =>
          some ⟨outS.1, HasTypeStmtCI.seq_return outS.2⟩
      | none =>
          match stmtReturnOut_of_profileLite P₂ with
          | some outT =>
              some ⟨outT.1, HasTypeStmtCI.seq_normal hN outT.2⟩
          | none =>
              none
  | .block P =>
      match blockReturnOut_of_profileLite P with
      | some out =>
          some ⟨Γ, HasTypeStmtCI.block out.2⟩
      | none =>
          none

def blockNormalOut_of_profileLite
    {Λ : TypeEnv} {ss : StmtBlock} :
    BlockBodyProfileLite Λ ss →
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK Λ ss Δ}
  | .nil =>
      some ⟨Λ, HasTypeBlockCI.nil⟩
  | .cons hN _ P₂ =>
      match blockNormalOut_of_profileLite P₂ with
      | some out =>
          some ⟨out.1, HasTypeBlockCI.cons_normal hN out.2⟩
      | none =>
          none

def blockReturnOut_of_profileLite
    {Λ : TypeEnv} {ss : StmtBlock} :
    BlockBodyProfileLite Λ ss →
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK Λ ss Δ}
  | .nil =>
      none
  | .cons hN P₁ P₂ =>
      match stmtReturnOut_of_profileLite P₁ with
      | some outS =>
          some ⟨outS.1, HasTypeBlockCI.cons_return outS.2⟩
      | none =>
          match blockReturnOut_of_profileLite P₂ with
          | some outT =>
              some ⟨outT.1, HasTypeBlockCI.cons_normal hN outT.2⟩
          | none =>
              none

end

def stmtSummary_of_profileLite
    {Γ : TypeEnv} {st : CppStmt}
    (P : StmtBodyProfileLite Γ st) :
    StmtBodySummary Γ st :=
  { normalOut := stmtNormalOut_of_profileLite P
    returnOut := stmtReturnOut_of_profileLite P }

def bodyControlProfile_of_profileLite
    {Γ : TypeEnv} {st : CppStmt}
    (P : StmtBodyProfileLite Γ st) :
    BodyControlProfile Γ st :=
  { summary := stmtSummary_of_profileLite P }


/-! ## 2. 観測命題層: lite adequacy -> flat soundness -/

mutual

theorem stmtNormalSound_of_lite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (P : StmtBodyProfileLite Γ st)
    (A : StmtBodyAdequacyLite Γ σ P) :
    ∀ {σ' : State},
      BigStepStmt σ st .normal σ' →
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
        stmtNormalOut_of_profileLite P = some out := by
  revert σ A
  cases P with
  | leaf S =>
      intro σ A σ' hstep
      cases A with
      | leaf hN hR =>
          simpa [stmtNormalOut_of_profileLite] using hN hstep
  | seq hN P₁ P₂ =>
      intro σ A σ' hstep
      cases A with
      | seq _ A₁ A₂ =>
          cases hstep with
          | seqNormal hS hT =>
              rcases stmtNormalSound_of_lite P₂ (A₂ hS) hT with ⟨out, hout⟩
              refine ⟨⟨out.1, HasTypeStmtCI.seq_normal hN out.2⟩, ?_⟩
              simp [stmtNormalOut_of_profileLite, hout]
  | block P =>
      intro σ A σ' hstep
      cases A with
      | block Ablk =>
          cases hstep with
          | block hopen hblk hclose =>
              rcases blockNormalSound_of_lite P (Ablk hopen) hblk with ⟨out, hout⟩
              refine ⟨⟨Γ, HasTypeStmtCI.block out.2⟩, ?_⟩
              simp [stmtNormalOut_of_profileLite, hout]

theorem stmtReturnSound_of_lite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (P : StmtBodyProfileLite Γ st)
    (A : StmtBodyAdequacyLite Γ σ P) :
    ∀ {rv : Option Value} {σ' : State},
      BigStepStmt σ st (.returnResult rv) σ' →
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
        stmtReturnOut_of_profileLite P = some out := by
  revert σ A
  cases P with
  | leaf S =>
      intro σ A rv σ' hstep
      cases A with
      | leaf hN hR =>
          simpa [stmtReturnOut_of_profileLite] using hR hstep
  | seq hN P₁ P₂ =>
      intro σ A rv σ' hstep
      cases A with
      | seq _ A₁ A₂ =>
          cases hstep with
          | seqReturn hS =>
              rcases stmtReturnSound_of_lite P₁ A₁ hS with ⟨outS, houtS⟩
              refine ⟨⟨outS.1, HasTypeStmtCI.seq_return outS.2⟩, ?_⟩
              simp [stmtReturnOut_of_profileLite, houtS]
          | seqNormal hS hT =>
              cases hRetP1 : stmtReturnOut_of_profileLite P₁ with
              | some outS =>
                  refine ⟨⟨outS.1, HasTypeStmtCI.seq_return outS.2⟩, ?_⟩
                  simp [stmtReturnOut_of_profileLite, hRetP1]
              | none =>
                  rcases stmtReturnSound_of_lite P₂ (A₂ hS) hT with ⟨outT, houtT⟩
                  refine ⟨⟨outT.1, HasTypeStmtCI.seq_normal hN outT.2⟩, ?_⟩
                  simp [stmtReturnOut_of_profileLite, hRetP1, houtT]
  | block P =>
      intro σ A rv σ' hstep
      cases A with
      | block Ablk =>
          cases hstep with
          | block hopen hblk hclose =>
              rcases blockReturnSound_of_lite P (Ablk hopen) hblk with ⟨out, hout⟩
              refine ⟨⟨Γ, HasTypeStmtCI.block out.2⟩, ?_⟩
              simp [stmtReturnOut_of_profileLite, hout]

theorem blockNormalSound_of_lite
    {Λ : TypeEnv} {σ : State} {ss : StmtBlock}
    (P : BlockBodyProfileLite Λ ss)
    (A : BlockBodyAdequacyLite Λ σ P) :
    ∀ {σ' : State},
      BigStepBlock σ ss .normal σ' →
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .normalK Λ ss Δ},
        blockNormalOut_of_profileLite P = some out := by
  revert σ A
  cases P with
  | nil =>
      intro σ A σ' hstep
      cases hstep
      refine ⟨⟨Λ, HasTypeBlockCI.nil⟩, ?_⟩
      simp [blockNormalOut_of_profileLite]
  | cons hN P₁ P₂ =>
      intro σ A σ' hstep
      cases A with
      | cons _ A₁ A₂ =>
          cases hstep with
          | consNormal hS hSs =>
              rcases blockNormalSound_of_lite P₂ (A₂ hS) hSs with ⟨out, hout⟩
              refine ⟨⟨out.1, HasTypeBlockCI.cons_normal hN out.2⟩, ?_⟩
              simp [blockNormalOut_of_profileLite, hout]

theorem blockReturnSound_of_lite
    {Λ : TypeEnv} {σ : State} {ss : StmtBlock}
    (P : BlockBodyProfileLite Λ ss)
    (A : BlockBodyAdequacyLite Λ σ P) :
    ∀ {rv : Option Value} {σ' : State},
      BigStepBlock σ ss (.returnResult rv) σ' →
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .returnK Λ ss Δ},
        blockReturnOut_of_profileLite P = some out := by
  revert σ A
  cases P with
  | nil =>
      intro σ A rv σ' hstep
      cases hstep
  | cons hN P₁ P₂ =>
      intro σ A rv σ' hstep
      cases A with
      | cons _ A₁ A₂ =>
          cases hstep with
          | consReturn hS =>
              rcases stmtReturnSound_of_lite P₁ A₁ hS with ⟨outS, houtS⟩
              refine ⟨⟨outS.1, HasTypeBlockCI.cons_return outS.2⟩, ?_⟩
              simp [blockReturnOut_of_profileLite, houtS]
          | consNormal hS hSs =>
              cases hRetP1 : stmtReturnOut_of_profileLite P₁ with
              | some outS =>
                  refine ⟨⟨outS.1, HasTypeBlockCI.cons_return outS.2⟩, ?_⟩
                  simp [blockReturnOut_of_profileLite, hRetP1]
              | none =>
                  rcases blockReturnSound_of_lite P₂ (A₂ hS) hSs with ⟨outT, houtT⟩
                  refine ⟨⟨outT.1, HasTypeBlockCI.cons_normal hN outT.2⟩, ?_⟩
                  simp [blockReturnOut_of_profileLite, hRetP1, houtT]

end


/-! ## 3. 組立層: flat CI adequacy / boundary assembly -/

noncomputable def stmtAdequacyCI_of_lite
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (P : StmtBodyProfileLite Γ st)
    (A : StmtBodyAdequacyLite Γ σ P) :
    BodyAdequacyCI Γ σ st (bodyControlProfile_of_profileLite P) := by
  refine
    { normalSound := ?_
      returnSound := ?_
      normalWitness := ?_
      returnWitness := ?_ }
  · intro σ' hstep
    exact stmtNormalSound_of_lite P A hstep
  · intro rv σ' hstep
    exact stmtReturnSound_of_lite P A hstep
  · intro σ' hstep
    let h := stmtNormalSound_of_lite P A hstep
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  · intro rv σ' hstep
    let h := stmtReturnSound_of_lite P A hstep
    exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def BodyClosureBoundaryLite.toBodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryLite Γ σ st)
    (root : BodyEntryWitness Γ st)
    (rootCoherent :
      BodyRootCoherent
        (bodyControlProfile_of_profileLite h.profile)
        root) :
    BodyReadyCI Γ σ st := by
  refine
    { structural :=
        { wf := h.structural.wf
          breakScoped := h.structural.breakScoped
          continueScoped := h.structural.continueScoped }
      static :=
        { typed0 := wellTypedFrom_of_profileLite h.profile
          profile := bodyControlProfile_of_profileLite h.profile
          root := root
          rootCoherent := rootCoherent }
      dynamic := h.dynamic
      adequacy := ?_ }
  exact stmtAdequacyCI_of_lite h.profile h.adequacy

noncomputable def BodyClosureBoundaryLite.toBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryLite Γ σ st)
    (root : BodyEntryWitness Γ st)
    (rootCoherent :
      BodyRootCoherent
        (bodyControlProfile_of_profileLite h.profile)
        root) :
    BodyClosureBoundaryCI Γ σ st := by
  refine
    { structural :=
        { wf := h.structural.wf
          breakScoped := h.structural.breakScoped
          continueScoped := h.structural.continueScoped }
      static :=
        { typed0 := wellTypedFrom_of_profileLite h.profile
          profile := bodyControlProfile_of_profileLite h.profile
          root := root
          rootCoherent := rootCoherent }
      dynamic := h.dynamic
      adequacy := ?_ }
  exact stmtAdequacyCI_of_lite h.profile h.adequacy

end Cpp
