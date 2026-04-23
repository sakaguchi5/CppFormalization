import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

/-!
# Closure.Foundation.BodyEntryWitnessCI

Canonical static CI entry payloads that can be threaded through assembled
boundaries without polluting the structural layer.

Design:
- `BodyStructuralBoundary` remains purely structural/coarse.
- assembled boundaries additionally carry one concrete CI entry witness.
- this is the minimal static payload needed by shape-specific consumers such as
  `while` entry decomposition.
-/

/-- One statically available CI channel for a top-level statement body. -/
inductive BodyEntryWitness (Γ : TypeEnv) (st : CppStmt) : Type where
  | normal
      (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}) :
      BodyEntryWitness Γ st
  | returned
      (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}) :
      BodyEntryWitness Γ st

/-- One statically available CI channel for an opened block body. -/
inductive BlockBodyEntryWitness (Γ : TypeEnv) (ss : StmtBlock) : Type where
  | normal
      (out : {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ}) :
      BlockBodyEntryWitness Γ ss
  | returned
      (out : {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ}) :
      BlockBodyEntryWitness Γ ss

namespace BodyEntryWitness

@[simp] def normalOut?
    {Γ : TypeEnv} {st : CppStmt}
    (e : BodyEntryWitness Γ st) :
    Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} :=
  match e with
  | .normal out => some out
  | .returned _ => none

@[simp] def returnOut?
    {Γ : TypeEnv} {st : CppStmt}
    (e : BodyEntryWitness Γ st) :
    Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} :=
  match e with
  | .normal _ => none
  | .returned out => some out

end BodyEntryWitness

namespace BlockBodyEntryWitness

@[simp] def normalOut?
    {Γ : TypeEnv} {ss : StmtBlock}
    (e : BlockBodyEntryWitness Γ ss) :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK (pushTypeScope Γ) ss Δ} :=
  match e with
  | .normal out => some out
  | .returned _ => none

@[simp] def returnOut?
    {Γ : TypeEnv} {ss : StmtBlock}
    (e : BlockBodyEntryWitness Γ ss) :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK (pushTypeScope Γ) ss Δ} :=
  match e with
  | .normal _ => none
  | .returned out => some out

end BlockBodyEntryWitness

end Cpp
