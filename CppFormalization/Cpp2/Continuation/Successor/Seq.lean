import CppFormalization.Cpp2.Continuation.Successor.Core
import CppFormalization.Cpp2.Continuation.Boundary.Seq

namespace Cpp
namespace ControlSuccessor

/-!
# Seq normal successor

C++ reading:

For a statement sequence

  left; right

if `left` exits normally, then `right` must be resumed under the post-left type
environment and post-left runtime state.

This file intentionally introduces only thin aliases over the existing seq
continuation boundary surfaces.  It does not introduce a fully generic dependent
successor target type.
-/

/-- The successor-kind tag for sequence normal flow. -/
def seqNormalSuccessorKind : SuccessorKind :=
  .seqNormal

/--
Dynamic successor for `left normal -> right`.

This is an alias of the existing dynamic seq-continuation compatibility surface.
-/
abbrev SeqNormalDynamicSuccessorCI :=
  SeqNormalContinuationDynamicCI

/--
Full boundary successor for `left normal -> right`.

This is an alias of the existing full seq-continuation boundary surface.
-/
abbrev SeqNormalBoundarySuccessorCI :=
  SeqNormalContinuationBoundaryCI

namespace SeqNormalDynamicSuccessorCI

/-- Compatibility projection back to the older continuation-dynamic name. -/
def toContinuationDynamic
    {Γ Θ : TypeEnv} {σ sigma1 : State} {left right : CppStmt}
    (S : SeqNormalDynamicSuccessorCI Γ Θ σ sigma1 left right) :
    SeqNormalContinuationDynamicCI Γ Θ σ sigma1 left right :=
  S

end SeqNormalDynamicSuccessorCI

namespace SeqNormalBoundarySuccessorCI

/-- Compatibility projection back to the older continuation-boundary name. -/
def toContinuationBoundary
    {Γ Θ : TypeEnv} {σ sigma1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ sigma1 left right) :
    SeqNormalContinuationBoundaryCI Γ Θ σ sigma1 left right :=
  S

end SeqNormalBoundarySuccessorCI

/--
Build the dynamic seq-normal successor from an explicit tail dynamic boundary.

C++ reading:
after `left` exits normally, resume `right` under the post-left environment
and state.
-/
def seqNormalDynamicSuccessor_of_tailDynamicBoundary
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (hleft : HasTypeStmtCI .normalK Γ left Θ)
    (hstepLeft : BigStepStmt σ left .normal σ1)
    (tail : StmtContinuationDynamicBoundary Θ σ1 right) :
    SeqNormalDynamicSuccessorCI Γ Θ σ σ1 left right :=
  seq_normal_continuation_dynamic_of_tail_dynamic_boundary
    hleft
    hstepLeft
    tail

/--
Build the full seq-normal successor from an existing tail closure boundary.

C++ reading:
after `left` exits normally, the successor target is the `right` statement
boundary under the post-left environment and state.
-/
def seqNormalBoundarySuccessor_of_tailClosureBoundary
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (hleft : HasTypeStmtCI .normalK Γ left Θ)
    (hstepLeft : BigStepStmt σ left .normal σ1)
    (tail : BodyClosureBoundaryCI Θ σ1 right) :
    SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right :=
  seq_normal_continuation_boundary_of_tail_closure_boundary
    hleft
    hstepLeft
    tail

namespace SeqNormalDynamicSuccessorCI

/-- Post-state validity exposed through the successor vocabulary. -/
theorem postState
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalDynamicSuccessorCI Γ Θ σ σ1 left right) :
    ScopedTypedStateConcrete Θ σ1 :=
  SeqNormalContinuationDynamicCI.postState S

/-- Tail readiness exposed through the successor vocabulary. -/
theorem tailReady
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalDynamicSuccessorCI Γ Θ σ σ1 left right) :
    StmtReadyConcrete Θ σ1 right :=
  SeqNormalContinuationDynamicCI.tailReady S

/-- Convert the dynamic successor to the ordinary body dynamic boundary. -/
def toBodyDynamicBoundary
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalDynamicSuccessorCI Γ Θ σ σ1 left right) :
    BodyDynamicBoundary Θ σ1 right :=
  SeqNormalContinuationDynamicCI.toBodyDynamicBoundary S

end SeqNormalDynamicSuccessorCI

namespace SeqNormalBoundarySuccessorCI

/-- Forget a full seq-normal successor to its dynamic successor. -/
def dynamic
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right) :
    SeqNormalDynamicSuccessorCI Γ Θ σ σ1 left right :=
  SeqNormalContinuationBoundaryCI.dynamic S

/-- Extract the successor target as a body closure boundary. -/
def tailBodyClosureBoundary
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right) :
    BodyClosureBoundaryCI Θ σ1 right :=
  SeqNormalContinuationBoundaryCI.tailBodyClosureBoundary S

/-- Extract the successor target as a body-ready entry. -/
def tailBodyReady
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right) :
    BodyReadyCI Θ σ1 right :=
  SeqNormalContinuationBoundaryCI.tailBodyReady S

/-- Tail readiness exposed through the successor vocabulary. -/
theorem tailReady
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right) :
    StmtReadyConcrete Θ σ1 right :=
  SeqNormalContinuationBoundaryCI.tailReady S

/-- Post-state validity exposed through the successor vocabulary. -/
theorem postState
    {Γ Θ : TypeEnv} {σ σ1 : State} {left right : CppStmt}
    (S : SeqNormalBoundarySuccessorCI Γ Θ σ σ1 left right) :
    ScopedTypedStateConcrete Θ σ1 :=
  SeqNormalContinuationBoundaryCI.postState S

end SeqNormalBoundarySuccessorCI

end ControlSuccessor
end Cpp
