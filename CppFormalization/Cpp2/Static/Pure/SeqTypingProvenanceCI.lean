import CppFormalization.Cpp2.Typing.ControlProfile

namespace Cpp

/-!
# Seq typing provenance

Pure sequence typing/profile provenance.

This file is intentionally allowed to live under `Static/Pure`: it contains only
state-free `HasTypeStmtCI` provenance and slot payloads.  It must not import
Closure boundary, readiness, semantics, state, or adequacy modules.
-/

/--
Normal channel provenance for a whole sequence payload.

This must live in `Prop`, not `Type`, because it is obtained by eliminating
a `HasTypeStmtCI` proof, and `HasTypeStmtCI` itself is a `Prop`.
-/
inductive SeqNormalSourceCI
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}) : Prop where
  | normal
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .normalK Θ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) :
      SeqNormalSourceCI out

/--
Return channel provenance for a whole sequence payload.

A sequence can return either because the left side returns, or because
the left side is normal and the tail returns.
-/
inductive SeqReturnSourceCI
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}) : Prop where
  | leftReturn
      {Δ : TypeEnv}
      (hleft : HasTypeStmtCI .returnK Γ s Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_return hleft⟩) :
      SeqReturnSourceCI out
  | tailReturn
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .returnK Θ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) :
      SeqReturnSourceCI out

theorem seq_normal_source_ci_of_out
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}) :
    SeqNormalSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | seq_normal hleft htail =>
      exact SeqNormalSourceCI.normal hleft htail rfl

theorem seq_return_source_ci_of_out
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}) :
    SeqReturnSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | seq_normal hleft htail =>
      exact SeqReturnSourceCI.tailReturn hleft htail rfl
  | seq_return hleft =>
      exact SeqReturnSourceCI.leftReturn hleft rfl

/-- Extract the left normal payload from a whole-sequence normal source. -/
theorem seq_normal_source_left_payload_ci
    {Γ : TypeEnv} {s t : CppStmt}
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (hsrc : SeqNormalSourceCI out) :
    ∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
      ∃ Δ, ∃ htail : HasTypeStmtCI .normalK Θ t Δ,
        out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩ := by
  cases hsrc with
  | normal hleft htail hout =>
      exact ⟨_, hleft, _, htail, hout⟩

/--
Extract the left-side payload required by a whole-sequence return source.

A left-return source gives a left return payload.  A tail-return source gives a
left normal payload, because the tail is reached only after the left side falls
through normally.
-/
theorem seq_return_source_left_payload_ci
    {Γ : TypeEnv} {s t : CppStmt}
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (hsrc : SeqReturnSourceCI out) :
    (∃ Δ, ∃ hleft : HasTypeStmtCI .returnK Γ s Δ,
        out = ⟨Δ, HasTypeStmtCI.seq_return hleft⟩) ∨
      (∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
        ∃ Δ, ∃ htail : HasTypeStmtCI .returnK Θ t Δ,
          out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) := by
  cases hsrc with
  | leftReturn hleft hout =>
      exact Or.inl ⟨_, hleft, hout⟩
  | tailReturn hleft htail hout =>
      exact Or.inr ⟨_, hleft, _, htail, hout⟩

/--
A Type-level normal slot for the extracted left profile.
-/
structure SeqLeftNormalSlotCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ

namespace SeqLeftNormalSlotCI

def out
    {Γ : TypeEnv} {s : CppStmt}
    (n : SeqLeftNormalSlotCI Γ s) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK Γ s Δ} :=
  ⟨n.Θ, n.hleft⟩

end SeqLeftNormalSlotCI

/--
A Type-level return slot for the extracted left profile.
-/
structure SeqLeftReturnSlotCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  Δ : TypeEnv
  hleft : HasTypeStmtCI .returnK Γ s Δ

namespace SeqLeftReturnSlotCI

def out
    {Γ : TypeEnv} {s : CppStmt}
    (r : SeqLeftReturnSlotCI Γ s) :
    {Δ : TypeEnv // HasTypeStmtCI .returnK Γ s Δ} :=
  ⟨r.Δ, r.hleft⟩

end SeqLeftReturnSlotCI

end Cpp
