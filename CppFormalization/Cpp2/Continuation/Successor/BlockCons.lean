import CppFormalization.Cpp2.Continuation.Successor.Core
import CppFormalization.Cpp2.Entry.Body.BlockBodyReadyAtCI

namespace Cpp
namespace ControlSuccessor

/-!
# Block cons normal successor

C++ reading:

For an opened block body

  head; tail

if `head` exits normally, then `tail` must be resumed under the post-head
type environment and post-head runtime state.
-/

/-- The successor-kind tag for opened block-body cons normal flow. -/
def blockConsNormalSuccessorKind : SuccessorKind :=
  .blockConsNormal

/--
Public successor vocabulary for opened block-body cons normal execution.

C++ reading:
for `head; tail`, if `head` exits normally, resume `tail`
under the post-head environment and state.

The underlying physical definition currently lives in
`Entry.Body.BlockBodyReadyAtCI` as `BlockBodyReadyAtCITailAfterHeadProvider`.
-/
abbrev BlockConsNormalSuccessorProvider : Type :=
  BlockBodyReadyAtCITailAfterHeadProvider


/-- Compatibility: use the new successor name where the old tail-after-head provider is expected. -/
def BlockConsNormalSuccessorProvider.toTailAfterHead
    (S : BlockConsNormalSuccessorProvider) :
    BlockBodyReadyAtCITailAfterHeadProvider :=
  S

/-- Compatibility: view the old provider as the new successor provider. -/
def BlockConsNormalSuccessorProvider.ofTailAfterHead
    (S : BlockBodyReadyAtCITailAfterHeadProvider) :
    BlockConsNormalSuccessorProvider :=
  S

namespace BlockConsNormalSuccessorProvider

/--
Compose a dynamic block-cons successor and a tail-entry rebuild provider.

This is the successor-name wrapper around the legacy
`BlockBodyReadyAtCITailAfterHeadProvider.ofDynamicAndRebuild`.
-/
def ofDynamicAndRebuild
    (tailDynamic : BlockBodyReadyAtCITailDynamicProvider)
    (tailRebuild : BlockBodyReadyAtCITailRebuildProvider) :
    BlockConsNormalSuccessorProvider :=
  BlockBodyReadyAtCITailAfterHeadProvider.ofDynamicAndRebuild
    tailDynamic
    tailRebuild

end BlockConsNormalSuccessorProvider


end ControlSuccessor
end Cpp
