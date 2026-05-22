import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Basic
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ReplayCore
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Entry
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Route.Condition
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Route.Body
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Progress.BodyLocal
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Backedge.PostState
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Backedge.ReplayInvariant
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Backedge.Continuation
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.Adequacy
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.ProofDemand
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Exit.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Surface

/-!
# CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2

Clean-room while closure scaffold.

This aggregate intentionally avoids importing the current while provider/kernel
modules.  It rebuilds the mathematical shape around entry, routes, backedge
replay, continuation, adequacy, and tail demand.
-/
