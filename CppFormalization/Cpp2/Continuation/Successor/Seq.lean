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

end ControlSuccessor
end Cpp
