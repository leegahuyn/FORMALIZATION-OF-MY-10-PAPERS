import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainSite
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleGenericField
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.EtaleFieldUnitLocalLift
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections

/-!
# The first generic-unit resolution remains exact under direct image

The affine integral charts cover the native affine étale site. Their
generic fibers are actual field spectra, where unit cokernel sections
lift. Thus the generic-point direct image of the unit cokernel
projection is an epimorphism of actual étale sheaves.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleGenericField SmallEtaleBaseChange KummerUnitsSheaf
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A F : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field F]
  [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev D := directImage (j A F) AddCommGrpCat.{0}

set_option maxHeartbeats 2600000 in
private theorem cokernel_projection_surjective_integral
    {M : Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}}
    (i : fullCoordinateUnitSheaf (Y F) ⟶ M) [Mono i]
    (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory) :
    Function.Surjective (((E A).inverse.map ((D A F).map (cokernel.π i))).hom.app (op U.obj)) := by
  let B : CommRingCat.{0} := unop U.obj.left
  let a : CommRingCat.of A ⟶ B := Spec.preimage U.obj.hom
  letI : Algebra A B := a.hom.toAlgebra
  letI : IsDomain B := U.property
  have ha : Spec.map a = U.obj.hom := Spec.map_preimage _
  have hEt : Etale (Spec.map a) := ha.symm ▸ U.obj.prop
  have he : (algebraMap A B).Etale := (HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp hEt
  letI : Algebra.Etale A B := RingHom.etale_algebraMap.mp he
  let W := algebraEtaleObject A B
  let V := (Scheme.AffineEtale.Spec (X A)).obj U.obj
  let e : W ≅ V := MorphismProperty.Over.isoMk (Iso.refl (Spec B)) (by
    change 𝟙 (Spec B) ≫ U.obj.hom = Spec.map (CommRingCat.ofHom (algebraMap A B))
    rw [Category.id_comp, show CommRingCat.ofHom (algebraMap A B) = a from CommRingCat.ofHom_hom a, ha])
  let H := etaleBaseChange (j A F)
  let L := F ⊗[A] B
  letI : Field L := (genericFiber_isField A B F).toField
  let S := Scheme.Etale.forget (Y F) ⋙ Over.forget (Y F)
  let e₀ : (H.obj V).left ≅ (H.obj W).left := S.mapIso (H.mapIso e.symm)
  let e₁ : (H.obj W).left ≅ Spec (CommRingCat.of L) := by
    let b := Spec.map (CommRingCat.ofHom (algebraMap A B))
    change pullback b (j A F) ≅ _
    exact pullbackSymmetry b (j A F) ≪≫ pullbackSpecIso A F B
  change Function.Surjective ((cokernel.π i).hom.app (op (H.obj V)))
  exact EtaleObjectRestriction.unitsCokernel_sections_surjective_of_field i (H.obj V) L (e₀ ≪≫ e₁)

set_option maxHeartbeats 2000000 in
/-- The actual direct-image map of a unit cokernel projection is epic. -/
theorem directImage_units_cokernel_π_epi
    {M : Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}}
    (i : fullCoordinateUnitSheaf (Y F) ⟶ M) [Mono i] :
    Epi ((D A F).map (cokernel.π i)) := by
  let S := Scheme.AffineEtale.topology (X A)
  let I := AffineEtaleDomainSite.inclusion A
  letI : I.IsCoverDense S := AffineEtaleDomainSite.integralCharts_coverDense A
  let R := (E A).inverse
  let m := (D A F).map (cokernel.π i)
  let n := R.map m
  letI : Sheaf.IsLocallySurjective n :=
    AffineEtaleLocalSurjectivity.of_coverDense S n.hom I (by
      intro U s
      obtain ⟨x, hx⟩ := cokernel_projection_surjective_integral A F i U s
      apply S.superset_covering _ (S.top_mem (I.obj U))
      intro V g _
      refine ⟨(R.obj ((D A F).obj M)).obj.map g.op x, ?_⟩
      rw [NatTrans.naturality_apply n.hom g.op x, hx])
  have h : Epi n := inferInstance
  exact R.epi_of_epi_map h

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GenericEtaleUnitSections.directImage_units_cokernel_π_epi
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
