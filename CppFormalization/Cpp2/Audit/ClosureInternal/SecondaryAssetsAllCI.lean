import CppFormalization.Cpp2.Adequacy.Body.BodyAdequacyCI
import CppFormalization.Cpp2.Audit.ClosureInternal.SecondarySeqAssetsCI
import CppFormalization.Cpp2.Metatheory.Closure.FunctionBodyCaseSplitCI
import CppFormalization.Cpp2.Legacy.ClosureInternal.SmallReusableWrappersCI
import CppFormalization.Cpp2.Metatheory.Closure.ProviderInterfacesCI
import CppFormalization.Cpp2.Metatheory.Closure.Unclassified.BlockExecutionBridgeTargetCI

/-!
# Closure.Internal.SecondaryAssetsAllCI

Aggregator for secondary assets.

Patch 1--4:
- sequence bundle/assets
- ite branch adequacy bridge
- small reusable wrappers
- provider interfaces

Patch 5:
- opened block execution bridge target
- opened block-body adequacy from that bridge
- block statement closure route using the explicit bridge

Provider-facing secondary assets:
- statement/block witness-producing adequacy providers
- Type-level ite slot inversion
- witness-producing branch adequacy to slot-aware support
-/
