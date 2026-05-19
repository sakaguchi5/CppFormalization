import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Continuation.Boundary.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Cons

/-!
# CppFormalization.Cpp2.Continuation

Continuation layer.

This layer contains selected execution routes and post-state continuation
boundaries.  The intended public subject is not a global readiness transport
theorem, but a route-indexed continuation boundary assembled from route data,
preservation, and route-local replay/stability contracts.
-/
