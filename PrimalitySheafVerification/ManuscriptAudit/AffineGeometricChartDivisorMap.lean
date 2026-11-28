import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorNaturality
import PrimalitySheafVerification.ManuscriptAudit.DedekindEtaleDivisorNaturality

/-!
# The actual divisor arrow on integral affine étale charts

The finite divisor of a unit in the generic fiber is a section of the
finite-support skyscraper sheaf. Its chart restriction is natural and
its kernel is the image of the actual regular unit sheaf.
-/

namespace ManuscriptAudit.AffineGeometricChartDivisorMap

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections DedekindEtaleGenericDivisor
open AffineGeometricDivisorSheaf AffineGeometricDivisorSections AffineGeometricDivisorNaturality

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K A B F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [CommRing B] [IsDomain B] [Field F]
  [Algebra A B] [Algebra.Etale A B] [Algebra A F] [IsFractionRing A F]

/-- The map from actual generic units to the divisor sheaf on the given integral chart. -/
def chartDivisorMap :
    genericUnitSectionGroup A B F →+
      (affineDivisorSheaf K A).obj.obj (op (chartObject A B)) :=
  (chartSectionsEquiv K A B).symm.toAddMonoidHom.comp (sectionDivisor A B F)

/-- The genuine regular units are exactly the kernel of the divisor
arrow to the actual finite-support skyscraper sheaf on this chart. -/
theorem chartDivisorMap_exact :
    Function.Exact
      ((genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B))).hom
      (chartDivisorMap K A B F) := by
  intro x
  let e := (chartSectionsEquiv K A B).symm
  change e (sectionDivisor A B F x) = 0 ↔ _
  rw [← e.map_zero, e.injective.eq_iff]
  exact genericPointUnitsHom_exact_onAffine A B F x

variable (C : Type) [CommRing C] [IsDomain C]
  [Algebra A C] [Algebra.Etale A C] [Algebra B C]
  [IsScalarTower A B C] [Algebra.Etale B C]

/-- The actual divisor arrow commutes with restrictions between integral
affine étale charts. -/
theorem chartDivisorMap_restrict (x : genericUnitSectionGroup A B F) :
    chartDivisorMap K A C F ((genericUnitImage A F).obj.map
      (algebraEtaleMap (IsScalarTower.toAlgHom A B C)).op x) =
    (affineDivisorSheaf K A).obj.map (chartArrow A B C).op (chartDivisorMap K A B F x) := by
  let e := chartSectionsEquiv K A B
  let e' := chartSectionsEquiv K A C
  apply e'.injective
  rw [chartSectionsEquiv_restrict]
  change e' (e'.symm (sectionDivisor A C F
      ((genericUnitImage A F).obj.map
        (algebraEtaleMap (IsScalarTower.toAlgHom A B C)).op x))) =
    AffineEtaleClosedPoints.pullback B C (e (e.symm (sectionDivisor A B F x)))
  rw [e'.apply_symm_apply, e.apply_symm_apply]
  exact (sectionDivisor_restrict A B C F x).symm

end

end ManuscriptAudit.AffineGeometricChartDivisorMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricChartDivisorMap.chartDivisorMap_exact,
      ``ManuscriptAudit.AffineGeometricChartDivisorMap.chartDivisorMap_restrict] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
