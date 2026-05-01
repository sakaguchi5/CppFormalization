import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.LoopBodyFunctionClosureCI

`while` body を top-level function body と混同しないための local closure shell.

重要:
- loop body は `break` / `continue` を合法な local exit として持つ。
- したがって top-level `BodyClosureBoundaryCI` の progress theorem ではなく、
  `LoopBodyBoundaryCI` 専用の local theorem surface を別に持つ。
- generic local closure 自体はまだ theorem-backed ではなく shell のままだが、
  replay-stable primitive body については top-level primitive closure を経由して
  theorem-backed に落とせる。
-/


/--
Local progress/divergence shell for a single loop body.

ここでの `ctrl` は raw statement control をそのまま残す。
`while` delimiter 側が `break` を吸収し、`return` を top-level へ通す。
-/
axiom loop_body_function_progress_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {body : CppStmt} :
    LoopBodyBoundaryCI Γ σ body →
    (∃ ctrl σ', BigStepStmt σ body ctrl σ') ∨ BigStepStmtDiv σ body

/-- replay-stable primitive body is a primitive-core concrete statement. -/
theorem replay_stable_primitive_stmt_is_primitive_core_concrete
    {st : CppStmt} :
    ReplayStablePrimitiveStmt st → PrimitiveCoreStmtConcrete st := by
  intro hstable
  cases st <;> simp [ReplayStablePrimitiveStmt, PrimitiveCoreStmtConcrete] at hstable ⊢

/-- replay-stable primitive body cannot terminate by raw return. -/
theorem replay_stable_primitive_stmt_no_return_local
    {σ σ' : State} {st : CppStmt} {rv : Option Value} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st (.returnResult rv) σ' := by
  intro hstable hret
  cases st <;> simp [ReplayStablePrimitiveStmt] at hstable <;> cases hret

/--
Turn a replay-stable primitive loop-body boundary into an honest top-level primitive boundary.

重要:
- `ReplayStablePrimitiveStmt` は `skip / exprStmt / assign` だけなので、
  top-level `breakScoped` / `continueScoped` は自明になる。
- typing は loop-body profile の `normalClosed` witness から old typing へ忘却する。
-/
def bodyReadyConcrete_of_replay_stable_primitive_loop_body
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (hstable : ReplayStablePrimitiveStmt body)
    (hloop : LoopBodyBoundaryCI Γ σ body) :
    BodyReadyConcrete Γ σ body := by
  have htyped0 : WellTypedFrom Γ body := by
    rcases hloop.profile.normalClosed with ⟨hN, _hsum⟩
    exact ⟨Γ, normalCI_to_old_stmt hN⟩
  have hbreakScoped : BreakWellScoped body := by
    cases body <;> simp [ReplayStablePrimitiveStmt] at hstable ⊢
    case skip => constructor
    case exprStmt => constructor
    case assign => constructor
  have hcontinueScoped : ContinueWellScoped body := by
    cases body <;> simp [ReplayStablePrimitiveStmt] at hstable ⊢
    case skip => constructor
    case exprStmt => constructor
    case assign => constructor
  exact
    { wf := hloop.structural.wf
      typed := htyped0
      breakScoped := hbreakScoped
      continueScoped := hcontinueScoped
      state := hloop.dynamic.state
      safe := hloop.dynamic.safe }

/--
Theorem-backed local progress/divergence for replay-stable primitive loop bodies.

数学的意味:
- generic loop-body local closure shell のうち、
  replay-stable primitive class については shell を消せる。
- 証明は top-level primitive closure theorem へ忘却し、
  function-body wrapper を raw statement control へ戻すだけでよい。

C++的意味:
- `skip / exprStmt / assign` の loop body は local abrupt exit を持たないので、
  top-level primitive closure と loop-body local closure が一致する。
-/
theorem replay_stable_primitive_loop_body_function_progress_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    LoopBodyBoundaryCI Γ σ body →
    (∃ ctrl σ', BigStepStmt σ body ctrl σ') ∨ BigStepStmtDiv σ body := by
  intro hstable hloop
  have hprim : PrimitiveCoreStmtConcrete body :=
    replay_stable_primitive_stmt_is_primitive_core_concrete hstable
  have htop :
      (∃ ex σ', BigStepFunctionBody σ body ex σ') ∨ BigStepStmtDiv σ body := by
    exact
      primitive_stmt_function_body_step_or_diverges_concrete_refined
        hprim
        (bodyReadyConcrete_of_replay_stable_primitive_loop_body hstable hloop)
  cases htop with
  | inl hfun =>
      rcases hfun with ⟨ex, σ', hfun⟩
      cases ex with
      | fellThrough =>
          exact Or.inl ⟨.normal, σ', by simpa using (BigStepFunctionBody.to_stmt hfun)⟩
      | returned rv =>
          have hret : BigStepStmt σ body (.returnResult rv) σ' := by
            simpa using (BigStepFunctionBody.to_stmt hfun)
          have hfalse : False :=
            replay_stable_primitive_stmt_no_return_local hstable hret
          exact False.elim hfalse
  | inr hdiv =>
      exact Or.inr hdiv

end Cpp
