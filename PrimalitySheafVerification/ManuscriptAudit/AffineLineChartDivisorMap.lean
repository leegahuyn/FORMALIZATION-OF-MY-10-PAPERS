import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorChartNaturality
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleDivisorNaturality

/-!
# The actual divisor arrow on integral affine étale charts

The finite divisor of a unit in the generic fiber is a section of the
finite-support skyscraper sheaf. Its chart restriction is natural and
its kernel is the image of the actual regular unit sheaf.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K B F : Type) [Field K] [IsAlgClosed K] [CommRing B] [IsDomain B] [Field F]
  [Algebra (Polynomial K) B] [Algebra.Etale (Polynomial K) B]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev A := Polynomial K

/-- The map from actual generic units to the divisor sheaf on the given integral chart. -/
def chartDivisorMap :
    genericUnitSectionGroup (A K) B F →+
      (affineDivisorSheaf K).obj.obj (op (chartObject K B)) :=
  (chartSectionsEquiv K B).symm.toAddMonoidHom.comp (sectionDivisor (A K) B F)

/-- The genuine regular units are exactly the kernel of the divisor
arrow to the actual finite-support skyscraper sheaf on this chart. -/
theorem chartDivisorMap_exact :
    Function.Exact
      ((genericPointUnitsHom (A K) F).hom.app (op (algebraEtaleObject (A K) B))).hom
      (chartDivisorMap K B F) := by
  intro x
  let e := (chartSectionsEquiv K B).symm
  change e (sectionDivisor (A K) B F x) = 0 ↔ _
  rw [← e.map_zero, e.injective.eq_iff]
  exact genericPointUnitsHom_exact_onAffine (A K) B F x

variable (C : Type) [CommRing C] [IsDomain C]
  [Algebra (A K) C] [Algebra.Etale (A K) C] [Algebra B C]
  [IsScalarTower (A K) B C] [Algebra.Etale B C]

/-- The actual divisor arrow commutes with restrictions between integral
affine étale charts. -/
theorem chartDivisorMap_restrict (x : genericUnitSectionGroup (A K) B F) :
    chartDivisorMap K C F ((genericUnitImage (A K) F).obj.map
      (algebraEtaleMap (IsScalarTower.toAlgHom (A K) B C)).op x) =
    (affineDivisorSheaf K).obj.map (chartArrow K B C).op (chartDivisorMap K B F x) := by
  let e := chartSectionsEquiv K B
  let e' := chartSectionsEquiv K C
  apply e'.injective
  rw [chartSectionsEquiv_restrict]
  change e' (e'.symm (sectionDivisor (A K) C F
      ((genericUnitImage (A K) F).obj.map
        (algebraEtaleMap (IsScalarTower.toAlgHom (A K) B C)).op x))) =
    AffineEtaleClosedPoints.pullback B C (e (e.symm (sectionDivisor (A K) B F x)))
  rw [e'.apply_symm_apply, e.apply_symm_apply]
  exact (sectionDivisor_restrict (A K) B C F x).symm

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.chartDivisorMap_exact,
      ``ManuscriptAudit.AffineLineDivisorSheaf.chartDivisorMap_restrict] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
