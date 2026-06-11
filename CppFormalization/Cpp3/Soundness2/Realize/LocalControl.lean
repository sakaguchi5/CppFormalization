import CppFormalization.Cpp3.Soundness2.Source.LocalControl

/-!
# CppFormalization.Cpp3.Soundness2.Realize.LocalControl

Realized local-control theorem bundle for the closed-internal Soundness2 route.

This is the first control handoff layer in the final route:

* `seq` exposes the tail boundary after a normally terminating sequence head;
* `blockTail` exposes the tail boundary after a normally terminating block head;
* `branch` selects the branch boundary after condition evaluation;
* `whileBody` exposes the body-entry boundary when a while condition is true;
* `whileBackedge` exposes the reentry boundary after normal/continue loop-body exit.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realizer bundle for all local-control source theorems. -/
structure LocalControlRealizationTheorems : Type where
  seq : Source.SeqTailControlSourceTheorem
  blockTail : Source.BlockTailControlSourceTheorem
  branch : Source.SelectedBranchControlSourceTheorem
  whileBody : Source.LoopBodyEntryControlSourceTheorem
  whileBackedge : Source.LoopBackedgeControlSourceTheorem

namespace LocalControlRealizationTheorems

/-- Convert realized local-control theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : LocalControlRealizationTheorems) :
    Source.LocalControlSourceTheorems where
  seq := R.seq
  blockTail := R.blockTail
  branch := R.branch
  whileBody := R.whileBody
  whileBackedge := R.whileBackedge

end LocalControlRealizationTheorems

end Realize
end Soundness2
end Cpp3
