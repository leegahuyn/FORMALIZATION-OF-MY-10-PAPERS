import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricChartDivisorLocalLift
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorHom

/-!
# Local surjectivity of the actual divisor morphism

Integral affine charts cover the affine site, and each divisor section
admits a lift after restriction to a principal open around each point.
The actual divisor morphism is therefore an epimorphism.
-/

namespace ManuscriptAudit.AffineGeometricDivisorHomEpi

open AlgebraicGeometry CategoryTheory Opposite
open AffineGeometricDivisorSheaf AffineGeometricDivisorHom
open AffineGeometricDivisorSections AffineGeometricDivisorNaturality
open AffineGeometricIntegralChartCoordinates AffineGeometricChartDivisorMap
open AffineGeometricChartDivisorLocalLift
open GenericEtaleUnitSections AffineEtaleLocalSurjectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X A)
private abbrev I := AffineEtaleDomainSite.inclusion A
private abbrev G := ((E A).inverse.obj (genericUnitImage A F)).obj
private abbrev D := (affineDivisorSheaf K A).obj

set_option maxHeartbeats 2200000 in
private theorem integralImageSieve_mem
    (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory)
    (d : (D K A).obj (op U.obj)) :
    Presheaf.imageSieve (affineDivisorHom K A F).hom d ∈ T A U.obj := by
  apply imageSieve_mem_of_pointwise (affineDivisorHom K A F).hom d
  intro x
  let B := coordinateRing A U.obj
  letI := coordinateAlgebra A U.obj
  letI := coordinateAlgebra_etale A U.obj
  letI : IsDomain B := U.property
  let e := coordinateChartIso A U.obj U.property
  let d' := (D K A).map e.hom.op d
  obtain ⟨b, hb, u, hu⟩ := chartDivisorMap_localLift K A B F x d'
  let C := Localization.Away b
  letI : IsDomain C := Localization.Away.isDomain (fun h ↦ hb (h.symm ▸ x.asIdeal.zero_mem))
  letI : Algebra.Etale B C := Algebra.Etale.of_isLocalizationAway b
  let a := chartArrow A B C
  let f := a ≫ e.hom
  let u₀ := (G A F).map e.inv.op u
  let m := (affineDivisorHom K A F).hom
  have hApp : m.app (op U.obj) =
      (G A F).map e.hom.op ≫ AddCommGrpCat.ofHom (chartDivisorMap K A B F) ≫
        (D K A).map e.inv.op :=
    affineDivisorHom_app_integral K A F U
  have hSource : (G A F).map e.inv.op ≫ (G A F).map e.hom.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id]
    exact (G A F).map_id _
  have hTarget : (D K A).map e.inv.op ≫ (D K A).map f.op = (D K A).map a.op := by
    have hF : f ≫ e.inv = a := by
      change (a ≫ e.hom) ≫ e.inv = a
      rw [Category.assoc, e.hom_inv_id]
      exact Category.comp_id a
    rw [← Functor.map_comp, ← op_comp, hF]
  have hTarget' : (D K A).map f.op = (D K A).map e.hom.op ≫ (D K A).map a.op := by
    rw [← Functor.map_comp, ← op_comp]
  refine ⟨chartObject A C, f, ?_, ?_⟩
  · refine ⟨(G A F).map f.op u₀, ?_⟩
    rw [NatTrans.naturality_apply, hApp]
    change (D K A).map f.op ((D K A).map e.inv.op
      (chartDivisorMap K A B F ((G A F).map e.hom.op ((G A F).map e.inv.op u)))) =
      (D K A).map f.op d
    have h₁ : (G A F).map e.hom.op ((G A F).map e.inv.op u) = u :=
      ConcreteCategory.congr_hom hSource u
    have h₂ : (D K A).map f.op ((D K A).map e.inv.op (chartDivisorMap K A B F u)) =
        (D K A).map a.op (chartDivisorMap K A B F u) :=
      ConcreteCategory.congr_hom hTarget (chartDivisorMap K A B F u)
    rw [h₁, h₂]
    exact hu.trans (ConcreteCategory.congr_hom hTarget' d).symm
  · let S := Scheme.AffineEtale.Spec (X A)
    have hS : (S.map f).left = Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [show f = a ≫ e.hom from rfl, S.map_comp]
      have hA : S.map a = algebraEtaleMap (IsScalarTower.toAlgHom A B C) :=
        S.map_preimage _
      rw [hA]
      change Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (𝟙 (coordinateRing A U.obj)) = _
      rw [Spec.map_id]
      exact Category.comp_id (Spec.map (CommRingCat.ofHom (algebraMap B C)))
    rw [hS]
    have hx : (show PrimeSpectrum B from x) ∈ Set.range (PrimeSpectrum.comap (algebraMap B C)) := by
      rw [PrimeSpectrum.localization_away_comap_range C b]
      exact hb
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (Spec.map_apply (CommRingCat.ofHom (algebraMap B C)) y).trans hy⟩

/-- The actual affine étale divisor morphism is an epimorphism. -/
theorem affineDivisorHom_epi : Epi (affineDivisorHom K A F) := by
  letI : (I A).IsCoverDense (T A) :=
    AffineEtaleDomainSite.integralCharts_coverDense A
  letI : Sheaf.IsLocallySurjective (affineDivisorHom K A F) :=
    of_coverDense (T A) (affineDivisorHom K A F).hom (I A)
      (integralImageSieve_mem K A F)
  infer_instance

/-- The actual divisor morphism on the full small étale site is epic. -/
theorem divisorHom_epi : Epi (divisorHom K A F) := by
  letI : Epi (affineDivisorHom K A F) := affineDivisorHom_epi K F
  unfold divisorHom
  infer_instance

end

end ManuscriptAudit.AffineGeometricDivisorHomEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricDivisorHomEpi.affineDivisorHom_epi,
      ``ManuscriptAudit.AffineGeometricDivisorHomEpi.divisorHom_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
