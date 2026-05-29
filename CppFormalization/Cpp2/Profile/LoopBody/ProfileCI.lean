import CppFormalization.Cpp2.Profile.ControlProfile

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.LoopBody.ProfileCI

State-free four-channel control profile for a single `while` body.

A loop body is not a top-level function body: `break` and `continue` are local
exits captured by the enclosing `while`.  Therefore the loop-body profile has
four channels: normal, break, continue, and return.
-/

/--
loop body の 4-channel summary.

`normal` / `break` / `continue` も `return` と同様に option で持つが、
`LoopBodyControlProfile` 側で while-compatible な closed-at-start witness を
明示的に要求する。
-/
structure LoopBodySummary (Γ : TypeEnv) (body : CppStmt) : Type where
  normalOut : Option {Δ : TypeEnv // HasTypeStmtCI .normalK Γ body Δ}
  breakOut : Option {Δ : TypeEnv // HasTypeStmtCI .breakK Γ body Δ}
  continueOut : Option {Δ : TypeEnv // HasTypeStmtCI .continueK Γ body Δ}
  returnOut : Option {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ}

/--
state-free 4-channel control profile for a loop body.

current CI typing では enclosing `while` が body に対して
- `normalK Γ body Γ`
- `breakK Γ body Γ`
- `continueK Γ body Γ`
を要求するので、その closed-at-start witness を profile の一部として固定する。
`return` だけは path-sensitive に残す。
-/
structure LoopBodyControlProfile (Γ : TypeEnv) (body : CppStmt) : Type where
  summary : LoopBodySummary Γ body
  normalClosed :
    { h : HasTypeStmtCI .normalK Γ body Γ //
      summary.normalOut = some ⟨Γ, h⟩ }
  breakClosed :
    { h : HasTypeStmtCI .breakK Γ body Γ //
      summary.breakOut = some ⟨Γ, h⟩ }
  continueClosed :
    { h : HasTypeStmtCI .continueK Γ body Γ //
      summary.continueOut = some ⟨Γ, h⟩ }

end Cpp
