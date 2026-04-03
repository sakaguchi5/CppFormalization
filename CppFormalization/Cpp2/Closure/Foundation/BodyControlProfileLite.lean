import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyControlProfileLite

E-lite 第一段階の control profile.

方針:
- flat な `normalOut / returnOut` のみを持つ summary を、そのまま主線には使わない。
- ただし一気に while まで full recursive にせず、seq / block body だけを syntax-mirroring にする。
- primitive / ite / while / return / break / continue などは、当面 `leaf` として残す。

目的:
- seq の tail transport を「whole-statement return witness の分解問題」ではなく、
  profile の projection 問題へ変える。
- block についても statement-level `.block` と opened block body を
  profile 上で honest に分ける。
-/

/--
Leaf statement 用の最小 summary.

ここでは既存の flat channel 形式を leaf に閉じ込める。
E-lite の主眼は seq / block の recursive node 化であり、
全 statement を一気に full recursive にしない。
-/
structure StmtLeafSummary (Γ : TypeEnv) (st : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}

mutual

/--
Top-level function body 用 lite control profile.

`seq` と `block` だけを syntax-mirroring にし、他は leaf に落とす。
`seq` node は left normal post-environment を明示的に保持する。
-/
inductive StmtBodyProfileLite : TypeEnv → CppStmt → Type where
  | leaf
      {Γ : TypeEnv} {st : CppStmt} :
      StmtLeafSummary Γ st →
      StmtBodyProfileLite Γ st

  | seq
      {Γ Δ : TypeEnv} {s t : CppStmt} :
      HasTypeStmtCI .normalK Γ s Δ →
      StmtBodyProfileLite Γ s →
      StmtBodyProfileLite Δ t →
      StmtBodyProfileLite Γ (.seq s t)

  | block
      {Γ : TypeEnv} {ss : StmtBlock} :
      BlockBodyProfileLite (pushTypeScope Γ) ss →
      StmtBodyProfileLite Γ (.block ss)

/--
Opened block body 用 lite control profile.

block body は `pushTypeScope Γ` 下で読み、`cons` ごとに left normal post-env を保持する。
-/
inductive BlockBodyProfileLite : TypeEnv → StmtBlock → Type where
  | nil
      {Γ : TypeEnv} :
      BlockBodyProfileLite Γ .nil

  | cons
      {Γ Δ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
      HasTypeStmtCI .normalK Γ s Δ →
      StmtBodyProfileLite Γ s →
      BlockBodyProfileLite Δ ss →
      BlockBodyProfileLite Γ (.cons s ss)

end

end Cpp
