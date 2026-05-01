import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Core.Syntax
namespace Cpp
--Core/Syntaxから
structure CoreBigStepCert : Type where
  Γ : TypeEnv
  σ : State
  st : CppStmt
  fragment : CoreBigStepFragment st
  closure : BodyClosureBoundaryCI Γ σ st

namespace CoreBigStepCert

def structural (c : CoreBigStepCert) :
    BodyStructuralBoundary c.Γ c.st :=
  c.closure.structural

def profile (c : CoreBigStepCert) :
    BodyControlProfile c.Γ c.st :=
  c.closure.static.profile

def dynamic (c : CoreBigStepCert) :
    BodyDynamicBoundary c.Γ c.σ c.st :=
  c.closure.dynamic

def bodyReadyCI (c : CoreBigStepCert) :
    BodyReadyCI c.Γ c.σ c.st :=
  c.closure.toBodyReadyCI

def bodyReady (c : CoreBigStepCert) :
    BodyReady c.Γ c.σ c.st :=
  c.closure.toBodyReady

@[simp] theorem bodyReadyCI_safe
    (c : CoreBigStepCert) :
    c.bodyReadyCI.dynamic.safe = c.dynamic.safe := by
  simp

@[simp] theorem bodyReadyCI_state
    (c : CoreBigStepCert) :
    c.bodyReadyCI.dynamic.state = c.dynamic.state := by
  simp

end CoreBigStepCert

end Cpp
