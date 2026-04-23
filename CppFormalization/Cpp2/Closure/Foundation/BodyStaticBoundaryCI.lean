import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyEntryWitnessCI
import CppFormalization.Cpp2.Typing.Stmt

namespace Cpp

/-!
# Closure.Foundation.BodyStaticBoundaryCI

Canonical static CI layer.

Purpose:
- make `entry` and `profile` one coherent object,
- keep old coarse typing (`typed0`) out of the structural layer,
- provide a single static source for shape-sensitive entry decomposition.
-/

structure BodyStaticBoundaryCI (Γ : TypeEnv) (st : CppStmt) : Type where
  typed0 : WellTypedFrom Γ st
  profile : BodyControlProfile Γ st
  root : BodyEntryWitness Γ st
  rootNormal :
    match root with
    | .normal out => profile.summary.normalOut = some out
    | .returned _ => True
  rootReturn :
    match root with
    | .returned out => profile.summary.returnOut = some out
    | .normal _ => True

structure BlockBodyStaticBoundaryCI (Γ : TypeEnv) (ss : StmtBlock) : Type where
  typed0 : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  profile : BlockBodyControlProfile Γ ss
  root : BlockBodyEntryWitness Γ ss
  rootNormal :
    match root with
    | .normal out => profile.summary.normalOut = some out
    | .returned _ => True
  rootReturn :
    match root with
    | .returned out => profile.summary.returnOut = some out
    | .normal _ => True

namespace BodyStaticBoundaryCI

@[simp] def normalOut?
    {Γ : TypeEnv} {st : CppStmt}
    (s : BodyStaticBoundaryCI Γ st) :
    Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} :=
  s.profile.summary.normalOut

@[simp] def returnOut?
    {Γ : TypeEnv} {st : CppStmt}
    (s : BodyStaticBoundaryCI Γ st) :
    Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} :=
  s.profile.summary.returnOut

@[simp] theorem root_normal_coherent
    {Γ : TypeEnv} {st : CppStmt}
    (s : BodyStaticBoundaryCI Γ st) :
    match s.root with
    | .normal out => s.normalOut? = some out
    | .returned _ => True := by
  simpa [normalOut?] using s.rootNormal

@[simp] theorem root_return_coherent
    {Γ : TypeEnv} {st : CppStmt}
    (s : BodyStaticBoundaryCI Γ st) :
    match s.root with
    | .returned out => s.returnOut? = some out
    | .normal _ => True := by
  -- 1. root についてケース分割し、同時に等式 h を得る
  -- 構造体そのものを分解して、内部の依存関係をバラバラにする
  cases s with | mk typed0 profile root rootNormal rootReturn =>
  cases root
  case returned out =>
    simp [returnOut?]
    -- ここで rootReturn は既に「profile.summary.returnOut = some out」という型に簡約されているはずです
    exact rootReturn
  case normal out =>
    simp

end BodyStaticBoundaryCI

namespace BlockBodyStaticBoundaryCI

@[simp] def normalOut?
    {Γ : TypeEnv} {ss : StmtBlock}
    (s : BlockBodyStaticBoundaryCI Γ ss) :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} :=
  s.profile.summary.normalOut

@[simp] def returnOut?
    {Γ : TypeEnv} {ss : StmtBlock}
    (s : BlockBodyStaticBoundaryCI Γ ss) :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} :=
  s.profile.summary.returnOut

@[simp] theorem root_normal_coherent
    {Γ : TypeEnv} {ss : StmtBlock}
    (s : BlockBodyStaticBoundaryCI Γ ss) :
    match s.root with
    | .normal out => s.normalOut? = some out
    | .returned _ => True := by
  simpa [normalOut?] using s.rootNormal

@[simp] theorem root_return_coherent
    {Γ : TypeEnv} {ss : StmtBlock}
    (s : BlockBodyStaticBoundaryCI Γ ss) :
    match s.root with
    | .returned out => s.returnOut? = some out
    | .normal _ => True := by
  -- 1. 構造体 s を構成要素に分解する
  cases s with | mk typed0 profile root rootNormal rootReturn =>
  -- 2. root フィールドの状態（normal か returned か）でケース分割する
  cases root
  case returned out =>
    -- match 文が簡約され、s.returnOut? (内部的には profile.summary.returnOut) の等式が残る
    simp [returnOut?]
    -- 依存型が解消された rootReturn を適用する
    exact rootReturn
  case normal out =>
    -- 左辺が True になるため、simp で終了
    simp

end BlockBodyStaticBoundaryCI

end Cpp
