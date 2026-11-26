import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Cohomology under the affine-to-full small étale equivalence

The native comparison of Ext groups applies to every abelian sheaf.
The source of the Ext group is matched by the constant-sheaf
comparison.
-/

namespace ManuscriptAudit.SmallEtaleCohomologyComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine and full small étale cohomology groups agree for every abelian sheaf. -/
def sheafCohomologyEquiv (R : CommRingCat.{0})
    (Y : Sheaf (Scheme.AffineEtale.topology (Spec R)) AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H Y n ≃+ Sheaf.H
      ((Scheme.AffineEtale.sheafEquiv (Spec R) AddCommGrpCat.{0}).functor.obj Y) n := by
  let J := Scheme.AffineEtale.topology (Spec R)
  let T := (Spec R).smallEtaleTopology
  let C := Sheaf J AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (Spec R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let F := (Scheme.AffineEtale.sheafEquiv (Spec R) AddCommGrpCat.{0}).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let X := (constantSheaf J AddCommGrpCat.{0}).obj Z
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom X Y n)
    (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)
  let e₁ := (((extFunctor (C := Sheaf T AddCommGrpCat.{0}) n).mapIso
    ((constantComparison R).app Z).symm.op).app (F.obj Y)).addCommGroupIsoToAddEquiv
  exact e₀.trans e₁

end

end ManuscriptAudit.SmallEtaleCohomologyComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleCohomologyComparison.sheafCohomologyEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
