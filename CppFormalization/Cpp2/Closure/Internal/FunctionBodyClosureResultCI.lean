import CppFormalization.Cpp2.Closure.Function.FunctionBody
import CppFormalization.Cpp2.Operational.Divergence

namespace Cpp

/-- Shared result type for function-body closure statements. -/
abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

end Cpp
