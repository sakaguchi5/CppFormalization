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
  c.closure.profile

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
    c.bodyReadyCI.safe = c.dynamic.safe :=
  rfl

@[simp] theorem bodyReadyCI_state
    (c : CoreBigStepCert) :
    c.bodyReadyCI.state = c.dynamic.state :=
  rfl

end CoreBigStepCert

end Cpp
