import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.SecondarySeqAssetsCI
import CppFormalization.Cpp2.Closure.Internal.IteBranchAdequacyAssetsCI
import CppFormalization.Cpp2.Closure.Internal.SmallReusableWrappersCI
import CppFormalization.Cpp2.Closure.Internal.ProviderInterfacesCI
import CppFormalization.Cpp2.Closure.Internal.BlockExecutionBridgeTargetCI

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

Witness-provider migration pre-patch:
- statement/block witness-producing adequacy providers
- Type-level ite slot inversion
- witness-producing branch adequacy to slot-aware support
-/
