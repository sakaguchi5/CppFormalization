import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfileLite
import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

/-!
# Closure.Foundation.BodyAdequacyLite

E-lite 第一段階の adequacy 層.

方針:
- flat profile に対する二本の soundness field ではなく、
  recursive profile に沿った adequacy witness を与える。
- seq node では
  * left part 自体の adequacy
  * left normal step 後に tail adequacy を再構成できる family
  を保持する。
- block node では opened scope の下の block-body adequacy family を保持する。

重要:
- ここでは seq / block の transport を profile 構造に埋め込み、
  flat `returnOut` 分解問題を回避する。
- while はまだ leaf 側に残し、この段階では hook を入れない。
-/

mutual
/-- 1. シグネチャの引数順を (Γ : TypeEnv) → (σ : State) に固定 -/
inductive StmtBodyAdequacyLite :
    (Γ : TypeEnv) → (σ : State) → {st : CppStmt} → StmtBodyProfileLite Γ st → Type where

  | leaf
      {Γ : TypeEnv} {σ : State} {st : CppStmt} {S : StmtLeafSummary Γ st} :
      (∀ {σ' : State},
        BigStepStmt σ st .normal σ' →
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
          S.normalOut = some out) →
      (∀ {rv : Option Value} {σ' : State},
        BigStepStmt σ st (.returnResult rv) σ' →
        ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
          S.returnOut = some out) →
      StmtBodyAdequacyLite Γ σ (.leaf S)

  | seq
      {Γ Δ : TypeEnv} {σ : State} {s t : CppStmt}
      {P₁ : StmtBodyProfileLite Γ s}
      {P₂ : StmtBodyProfileLite Δ t}
      (hN : HasTypeStmtCI .normalK Γ s Δ) :
      -- ここで渡す引数の順序が、上記の定義順と一致しているか確認
      StmtBodyAdequacyLite Γ σ P₁ →
      (∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        StmtBodyAdequacyLite Δ σ' P₂) →
      StmtBodyAdequacyLite Γ σ (.seq hN P₁ P₂)

  | block
      {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
      {P : BlockBodyProfileLite (pushTypeScope Γ) ss} :
      (∀ {σ' : State},
        OpenScope σ σ' →
        BlockBodyAdequacyLite (pushTypeScope Γ) σ' P) →
      StmtBodyAdequacyLite Γ σ (.block P)

/-- 2. Block側も同様の順序にする -/
inductive BlockBodyAdequacyLite :
    (Γ : TypeEnv) → (σ : State) → {ss : StmtBlock} → BlockBodyProfileLite Γ ss → Type where

  | nil {Γ : TypeEnv} {σ : State} :
      BlockBodyAdequacyLite Γ σ .nil

  | cons
      {Γ Δ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
      {P₁ : StmtBodyProfileLite Γ s}
      {P₂ : BlockBodyProfileLite Δ ss}
      (hN : HasTypeStmtCI .normalK Γ s Δ) :
      StmtBodyAdequacyLite Γ σ P₁ →
      (∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        BlockBodyAdequacyLite Δ σ' P₂) →
      BlockBodyAdequacyLite Γ σ (.cons hN P₁ P₂)

end

end Cpp
