import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyPrimitiveClosureCI

Primitive statement cases for CI-centric function-body closure.

役割:
- `BodyReadyCI` / `BodyClosureBoundaryCI` から concrete refined boundary へ忘却する。
- primitive statement case だけは theorem-backed なので、
  case-driver や higher closure layer から共通に読める場所へ切り出す。
- これにより `FunctionBodyCaseDriverCI` が `FunctionBodyClosureCI` に依存せずに済み、
  global recursion shell を `CurrentShellCI` に入れても import cycle を起こさない。
-/


/-- Forget the CI-sensitive fields and recover the existing refined concrete boundary. -/
theorem bodyReadyConcrete_of_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyReadyCI Γ σ st → BodyReadyConcrete Γ σ st := by
  intro h
  exact {
    wf := h.structural.wf
    typed := h.static.typed0
    breakScoped := h.structural.breakScoped
    continueScoped := h.structural.continueScoped
    state := h.dynamic.state
    safe := h.dynamic.safe
  }

/-- forgetful map from the new assembled boundary to the refined concrete boundary. -/
theorem bodyReadyConcrete_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyClosureBoundaryCI Γ σ st → BodyReadyConcrete Γ σ st := by
  intro h
  exact bodyReadyConcrete_of_bodyReadyCI h.toBodyReadyCI

/-- Primitive case already follows from the refined concrete layer once we forget CI extras. -/
theorem primitive_stmt_function_body_step_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hprim hready
  exact
    primitive_stmt_function_body_step_or_diverges_concrete_refined
      hprim (bodyReadyConcrete_of_bodyReadyCI hready)

/-- entry version of the primitive case. -/
theorem primitive_stmt_function_body_step_or_diverges_body_closure
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hprim hready
  exact
    primitive_stmt_function_body_step_or_diverges_concrete_refined
      hprim (bodyReadyConcrete_of_bodyClosureBoundaryCI hready)

end Cpp
