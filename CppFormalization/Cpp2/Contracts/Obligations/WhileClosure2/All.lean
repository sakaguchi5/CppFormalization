import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Basic
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ReplayCore
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Entry
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ConditionRoute
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BodyRoute
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ExitLifting
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BackedgeReplay
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BackedgeContinuation
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.TailAdequacy
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.TailDemand
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Surface

/-!
# CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2

Clean-room while closure scaffold.

This aggregate intentionally avoids importing the current while provider/kernel
modules.  It rebuilds the mathematical shape around entry, routes, backedge
replay, continuation, adequacy, and tail demand.
-/
