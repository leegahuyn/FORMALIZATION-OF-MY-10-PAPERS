import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorExtAdjunction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleFreeRepresentable

/-!
# Ambient cohomology at an open object and cohomology on the open

Use the actual open immersion, its restriction, and its extension by
zero in the small étale topologies. The free representable sheaf and
the exact Ext adjunction identify the native cohomology presheaf
value on the open with its ordinary cohomology.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ExactFunctorDerivedAdjunction GeometricSkyscraperCohomology

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

/-- All degrees of the actual étale cohomology presheaf evaluated on the
open identify additively with ordinary small étale cohomology on the open. -/
def openCohomologyPresheafEquiv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology C.{u}) (n : ℕ) :
    F.H' n (Scheme.Etale.mk j) ≃+ Sheaf.H ((restriction j C.{u}).obj F) n := by
  let E := extensionByZero j C.{u}
  let R := restriction j C.{u}
  letI : E.Additive := extensionByZero_additive j
  letI : R.Additive := restriction_additive j
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  letI : PreservesFiniteColimits E := (extensionByZero_exact j).2
  letI : PreservesFiniteLimits R := (restriction_exact j).1
  letI : PreservesFiniteColimits R := (restriction_exact j).2
  let A := (freeEtaleRepresentable X).obj (Scheme.Etale.mk j)
  let Z := (constantSheaf U.smallEtaleTopology C.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let e : A ≅ E.obj Z := freeEtaleRepresentableOpenIso j
  let e' := ((extFunctor (C := Sheaf X.smallEtaleTopology C.{u}) n).mapIso e.symm.op).app F
  let x : Ext A F n ≃+ Ext (E.obj Z) F n := e'.addCommGroupIsoToAddEquiv
  change Ext A F n ≃+ Ext Z (R.obj F) n
  exact x.trans (extAdjunction (abelianExtensionByZeroAdjunction j) Z F n)

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleExtension.openCohomologyPresheafEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
