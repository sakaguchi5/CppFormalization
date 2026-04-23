import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility

namespace Cpp

/-- Legacy runtime-side package: for now, this only carries the dynamic boundary. -/
structure RuntimePiecesLegacy (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  dynamic : BodyDynamicBoundary Γ σ st

/-- Legacy reflection-side package: keep structural and profile chosen together. -/
structure ReflectionPiecesLegacy (Γ : TypeEnv) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  entry : BodyEntryWitness Γ st
  profile : BodyControlProfile Γ st

/--
Legacy std fragment interface.

Minimal upgrade:
- keep the old predicate names (`uses`, `establishesDynamic`);
- add a constructor returning the actual runtime package.
-/
structure VerifiedStdFragment where
  Name : Type
  uses : Name → Prop
  establishesDynamic : Name → TypeEnv → State → CppStmt → Prop

  mkRuntime :
    ∀ {n : Name} {Γ : TypeEnv} {σ : State} {st : CppStmt},
      uses n →
      establishesDynamic n Γ σ st →
      RuntimePiecesLegacy Γ σ st

/--
Legacy reflection fragment interface.

Minimal upgrade:
- keep the old predicate names (`generates`, `establishesStructural`, `establishesProfile`);
- add a constructor returning the actual reflection package.
-/
structure VerifiedReflectionFragment where
  Meta : Type
  generates : Meta → CppStmt → Prop
  establishesStructural : Meta → TypeEnv → CppStmt → Prop
  establishesProfile : Meta → TypeEnv → CppStmt → Prop

  mkReflection :
    ∀ {m : Meta} {Γ : TypeEnv} {st : CppStmt},
      generates m st →
      establishesStructural m Γ st →
      establishesProfile m Γ st →
      ReflectionPiecesLegacy Γ st

/--
The only legacy glue that remains genuinely external:
given the std-side runtime assumptions and the reflection-side chosen package,
produce adequacy for that chosen canonical profile.
-/
structure VerifiedExternalGlueLegacy
    (F : VerifiedStdFragment) (R : VerifiedReflectionFragment) where
  compatible : F.Name → R.Meta → TypeEnv → State → CppStmt → Prop

  mkAdequacy :
    ∀ {n : F.Name} {m : R.Meta}
      {Γ : TypeEnv} {σ : State} {st : CppStmt},
      (huse : F.uses n) →
      (hdyn : F.establishesDynamic n Γ σ st) →
      (hgen : R.generates m st) →
      (hstruct : R.establishesStructural m Γ st) →
      (hprof : R.establishesProfile m Γ st) →
      (hcompat : compatible n m Γ σ st) →
      BodyAdequacyCI Γ σ st
        ((R.mkReflection (m := m) (Γ := Γ) (st := st) hgen hstruct hprof).profile)

/--
Still keep this as the remaining core-membership bridge for the legacy interface.

This can be removed later if `ReflectionPiecesLegacy` is extended with
`core : CoreBigStepFragment st`.
-/
axiom reflection_fragment_generates_core
    {R : VerifiedReflectionFragment} {m : R.Meta} {st : CppStmt} :
    R.generates m st →
    CoreBigStepFragment st

/--
Assembled boundary is no longer axiomatic.
It is built definitionally from:
- std-side runtime package,
- reflection-side structural/profile package,
- glue-produced adequacy.
-/
noncomputable def fragments_establish_body_closure_boundary
    {F : VerifiedStdFragment} {R : VerifiedReflectionFragment}
    (G : VerifiedExternalGlueLegacy F R)
    {n : F.Name} {m : R.Meta}
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (huse : F.uses n)
    (hdyn : F.establishesDynamic n Γ σ st)
    (hgen : R.generates m st)
    (hstruct : R.establishesStructural m Γ st)
    (hprof : R.establishesProfile m Γ st)
    (hcompat : G.compatible n m Γ σ st) :
    BodyClosureBoundaryCI Γ σ st := by
  let hrun : RuntimePiecesLegacy Γ σ st :=
    F.mkRuntime huse hdyn
  let hrefl : ReflectionPiecesLegacy Γ st :=
    R.mkReflection hgen hstruct hprof
  let hadeq : BodyAdequacyCI Γ σ st hrefl.profile :=
    G.mkAdequacy huse hdyn hgen hstruct hprof hcompat
  exact
    mkBodyClosureBoundaryCI
      hrefl.structural
      hrefl.entry
      hrefl.profile
      hrun.dynamic
      hadeq

end Cpp
