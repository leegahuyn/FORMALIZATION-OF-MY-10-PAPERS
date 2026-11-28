import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOverDedekind
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleGenericField
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitComparison

/-!
# Exactness at the actual generic-point unit sections

On an integral affine étale chart over any Dedekind domain, the
generic-point direct image consists of units of the coordinate ring's
fraction field. Its vanishing height-one divisor criterion cuts out
the image of regular units of the actual chart.
-/

namespace ManuscriptAudit.DedekindEtaleGenericDivisor

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleGenericField DedekindPrincipalDivisor KummerUnitsSheaf
open GenericEtaleUnitSections
open IsDedekindDomain
open scoped TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B F : Type) [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDomain B] [Field F] [Algebra A B] [Algebra A F]
  [IsFractionRing A F] [Algebra.Etale A B]

/-- The actual generic-point direct-image sections on the specified chart. -/
abbrev genericUnitSectionGroup :=
  (genericUnitImage A F).obj.obj (op (algebraEtaleObject A B))

/-- The divisor map on sections of the actual generic-point direct image. -/
def sectionDivisor : genericUnitSectionGroup A B F →+ (HeightOneSpectrum B →₀ ℤ) := by
  let L := F ⊗[A] B
  letI : Field L := (genericFiber_isField A B F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  letI : IsDedekindDomain B := AffineEtaleOverDedekind.isDedekindDomain A B
  exact (principalDivisor B L).comp (genericUnitSectionsIso A B F).hom.hom

/-- On each integral affine étale chart, vanishing of the actual divisor
is equivalent to belonging to the image of regular units. -/
theorem genericPointUnitsHom_exact_onAffine :
    Function.Exact
      ((genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B))).hom
      (sectionDivisor A B F) := by
  let L := F ⊗[A] B
  letI : Field L := (genericFiber_isField A B F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  letI : IsDedekindDomain B := AffineEtaleOverDedekind.isDedekindDomain A B
  let eU := (affineUnitSectionsIso A B).addCommGroupIsoToAddEquiv
  let eL := (genericUnitSectionsIso A B F).addCommGroupIsoToAddEquiv
  let q := ((genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B))).hom
  have hQ (x : (fullCoordinateUnitSheaf (Spec (CommRingCat.of A))).obj.obj
      (op (algebraEtaleObject A B))) :
      eL (q x) = unitInclusion B L (eU x) := by
    exact ConcreteCategory.congr_hom (genericPointUnitsHom_onAffine A B F) x
  intro y
  change principalDivisor B L (eL y) = 0 ↔ ∃ x, q x = y
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (principalDivisor_exact B L (eL y)).1 h
    refine ⟨eU.symm u, eL.injective ?_⟩
    rw [hQ, eU.apply_symm_apply, hu]
  · rintro ⟨x, rfl⟩
    rw [hQ]
    exact (principalDivisor_exact B L _).2 ⟨eU x, rfl⟩

end

end ManuscriptAudit.DedekindEtaleGenericDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.DedekindEtaleGenericDivisor.genericPointUnitsHom_exact_onAffine
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
