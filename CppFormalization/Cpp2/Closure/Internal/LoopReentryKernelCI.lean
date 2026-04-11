import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCompatibility

namespace Cpp

/-!
# Closure.Internal.LoopReentryKernelCI

`while` header への再入法則。

`LoopBodyBoundaryCI` は body 自身の local 4-channel contract を表す。
このファイルの `LoopReentryKernelCI` は、それとは別に

- body の `normal` / `continue` 実行後に condition が post-state で再び ready になること
- body 自身の local contract が post-state で再構成できること

をまとめる。

重要:
- `break` は re-entry を起こさず enclosing `while` に吸収されるので、ここでは扱わない。
- `return` は enclosing `while` を突き抜けるので、ここでも扱わない。
-/

/--
A while-specific kernel describing how one iteration re-enters the header.

This is not a loop-body local property.
It belongs to the delimiter (`while`) because it mentions the condition and the
post-step reconstruction of the *next* iteration boundary.
-/
structure LoopReentryKernelCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  hc : HasValueType Γ c (.base .bool)

  /-- condition replay after a normal body step. -/
  cond_after_normal :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .normal σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

  /-- condition replay after a continue body step. -/
  cond_after_continue :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

  /-- local loop-body contract reconstructed after a normal body step. -/
  body_after_normal :
    ∀ {σ σ' : State},
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .normal σ' →
      LoopBodyBoundaryCI Γ σ' body

  /-- local loop-body contract reconstructed after a continue body step. -/
  body_after_continue :
    ∀ {σ σ' : State},
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyBoundaryCI Γ σ' body

namespace LoopReentryKernelCI

/-- recover the post-state loop-body boundary after a normal body step. -/
def nextBody_after_normal
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    LoopBodyBoundaryCI Γ σ' body :=
  K.body_after_normal hbody hstep

/-- recover the post-state loop-body boundary after a continue body step. -/
def nextBody_after_continue
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    LoopBodyBoundaryCI Γ σ' body :=
  K.body_after_continue hbody hstep

/-- reconstruct `while` readiness after a normal body step. -/
def whileReady_after_normal
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let hbody' : LoopBodyBoundaryCI Γ σ' body :=
    K.nextBody_after_normal hbody hstep
  let hcond' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    K.cond_after_normal hcond hbody hstep
  exact StmtReadyConcrete.whileStmt K.hc hcond' hbody'.dynamic.safe

/-- reconstruct `while` readiness after a continue body step. -/
def whileReady_after_continue
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  let hbody' : LoopBodyBoundaryCI Γ σ' body :=
    K.nextBody_after_continue hbody hstep
  let hcond' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    K.cond_after_continue hcond hbody hstep
  exact StmtReadyConcrete.whileStmt K.hc hcond' hbody'.dynamic.safe

/-- dynamic entry boundary for the tail `while` after a normal body step. -/
def whileDynamic_after_normal
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    BodyDynamicBoundary Γ σ' (.whileStmt c body) := by
  let hbody' : LoopBodyBoundaryCI Γ σ' body :=
    K.nextBody_after_normal hbody hstep
  refine
    { state := hbody'.dynamic.state
      safe := K.whileReady_after_normal hcond hbody hstep }

/-- dynamic entry boundary for the tail `while` after a continue body step. -/
def whileDynamic_after_continue
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    {σ σ' : State}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    BodyDynamicBoundary Γ σ' (.whileStmt c body) := by
  let hbody' : LoopBodyBoundaryCI Γ σ' body :=
    K.nextBody_after_continue hbody hstep
  refine
    { state := hbody'.dynamic.state
      safe := K.whileReady_after_continue hcond hbody hstep }

end LoopReentryKernelCI

end Cpp
