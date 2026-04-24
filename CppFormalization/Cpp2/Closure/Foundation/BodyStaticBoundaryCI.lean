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

inductive BodyRootCoherent
    {Γ : TypeEnv} {st : CppStmt}
    (profile : BodyControlProfile Γ st) :
    BodyEntryWitness Γ st → Prop where
  | normal {out} :
      profile.summary.normalOut = some out →
      BodyRootCoherent profile (.normal out)
  | returned {out} :
      profile.summary.returnOut = some out →
      BodyRootCoherent profile (.returned out)

inductive BlockBodyRootCoherent
    {Γ : TypeEnv} {ss : StmtBlock}
    (profile : BlockBodyControlProfile Γ ss) :
    BlockBodyEntryWitness Γ ss → Prop where
  | normal {out} :
      profile.summary.normalOut = some out →
      BlockBodyRootCoherent profile (.normal out)
  | returned {out} :
      profile.summary.returnOut = some out →
      BlockBodyRootCoherent profile (.returned out)


structure BodyStaticBoundaryCI (Γ : TypeEnv) (st : CppStmt) : Type where
  typed0 : WellTypedFrom Γ st
  profile : BodyControlProfile Γ st
  root : BodyEntryWitness Γ st
  rootCoherent : BodyRootCoherent profile root

structure BlockBodyStaticBoundaryCI (Γ : TypeEnv) (ss : StmtBlock) : Type where
  typed0 : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  profile : BlockBodyControlProfile Γ ss
  root : BlockBodyEntryWitness Γ ss
  rootCoherent : BlockBodyRootCoherent profile root

@[simp] theorem BodyStaticBoundaryCI.root_normal_coherent
    {Γ : TypeEnv} {st : CppStmt}
    (h : BodyStaticBoundaryCI Γ st) :
    match h.root with
    | .normal out => h.profile.summary.normalOut = some out
    | .returned _ => True := by
  rcases h with ⟨typed0, profile, root, hc⟩
  cases hc with
  | normal hN =>
      exact hN
  | returned hR =>
      trivial

@[simp] theorem BodyStaticBoundaryCI.root_return_coherent
    {Γ : TypeEnv} {st : CppStmt}
    (h : BodyStaticBoundaryCI Γ st) :
    match h.root with
    | .returned out => h.profile.summary.returnOut = some out
    | .normal _ => True := by
  rcases h with ⟨typed0, profile, root, hc⟩
  cases hc with
  | normal hN =>
      trivial
  | returned hR =>
      exact hR

@[simp] theorem BlockBodyStaticBoundaryCI.root_normal_coherent
    {Γ : TypeEnv} {ss : StmtBlock}
    (h : BlockBodyStaticBoundaryCI Γ ss) :
    match h.root with
    | .normal out => h.profile.summary.normalOut = some out
    | .returned _ => True := by
  rcases h with ⟨typed0, profile, root, hc⟩
  cases hc with
  | normal hN =>
      exact hN
  | returned hR =>
      trivial

@[simp] theorem BlockBodyStaticBoundaryCI.root_return_coherent
    {Γ : TypeEnv} {ss : StmtBlock}
    (h : BlockBodyStaticBoundaryCI Γ ss) :
    match h.root with
    | .returned out => h.profile.summary.returnOut = some out
    | .normal _ => True := by
  rcases h with ⟨typed0, profile, root, hc⟩
  cases hc with
  | normal hN =>
      trivial
  | returned hR =>
      exact hR

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

end BlockBodyStaticBoundaryCI

end Cpp
