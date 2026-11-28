import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorFullExact

/-! The genuine generic-unit-to-divisor quotient comparison preserves
the actual divisor morphism, including after passing to the affine basis. -/

namespace ManuscriptAudit.AffineGeometricQuotientProjection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections AffineGeometricDivisorSheaf
open AffineGeometricDivisorHom AffineGeometricDivisorFullExact

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}

/-- The actual cokernel point isomorphism carries the quotient projection
to the genuine divisorial morphism of sheaves. -/
theorem full_quotient_projection :
    cokernel.π (genericPointUnitsHom A F) ≫ (genericPointUnitQuotientIsoDivisor K A F).hom =
      divisorHom K A F := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (genericPointUnitsHom A F))
    (divisorSequence_shortExact K A F).gIsCokernel WalkingParallelPair.one

private theorem map_counit_inv (M : Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0}) :
    (E A).inverse.map ((E A).counitIso.inv.app M) =
      (E A).unitIso.hom.app ((E A).inverse.obj M) := by
  apply (cancel_mono ((E A).unitIso.inv.app ((E A).inverse.obj M))).mp
  rw [(E A).inverse_counitInv_comp, (E A).unitIso_hom_inv_id_app]

private theorem divisorHom_on_basis :
    (E A).inverse.map (divisorHom K A F) ≫ (restrictionIso K A).hom =
      affineDivisorHom K A F := by
  let d := affineDivisorHom K A F
  let M := genericUnitImage A F
  change (E A).inverse.map (((E A).counitIso.app M).inv ≫ (E A).functor.map d) ≫
    (E A).unitIso.inv.app (affineDivisorSheaf K A) = d
  rw [Functor.map_comp, Category.assoc, map_counit_inv]
  have h := (E A).unitIso.inv.naturality d
  change (E A).inverse.map ((E A).functor.map d) ≫
      (E A).unitIso.inv.app (affineDivisorSheaf K A) =
    (E A).unitIso.inv.app ((E A).inverse.obj M) ≫ d at h
  rw [h, (E A).unitIso_hom_inv_id_app_assoc]

/-- After restricting to the native affine basis, the quotient comparison
still takes the literal quotient projection to the actual divisor hom. -/
theorem affine_quotient_projection :
    (E A).inverse.map (cokernel.π (genericPointUnitsHom A F)) ≫
        ((E A).inverse.mapIso (genericPointUnitQuotientIsoDivisor K A F) ≪≫
          restrictionIso K A).hom =
      affineDivisorHom K A F := by
  rw [Iso.trans_hom, ← Category.assoc]
  change _ ≫ (restrictionIso K A).hom = _
  rw [← Functor.map_comp, full_quotient_projection]
  exact divisorHom_on_basis K A F

end

end ManuscriptAudit.AffineGeometricQuotientProjection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricQuotientProjection.full_quotient_projection,
      ``ManuscriptAudit.AffineGeometricQuotientProjection.affine_quotient_projection] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
