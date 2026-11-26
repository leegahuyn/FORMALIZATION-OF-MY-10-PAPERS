import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.AffineLineChartDivisorLocalLift
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHom

/-!
# Local surjectivity of the actual divisor morphism

Integral affine charts cover the affine site, and each divisor section
admits a lift after restriction to a principal open around each point.
The actual divisor morphism is therefore an epimorphism.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections AffineEtaleLocalSurjectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev A := Polynomial K
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X K)
private abbrev I := AffineEtaleDomainSite.inclusion (A K)
private abbrev G := ((E K).inverse.obj (genericUnitImage (A K) F)).obj
private abbrev D := (affineDivisorSheaf K).obj

set_option maxHeartbeats 2200000 in
private theorem integralImageSieve_mem
    (U : (AffineEtaleDomainSite.integralCharts (A K)).FullSubcategory)
    (d : (D K).obj (op U.obj)) :
    Presheaf.imageSieve (affineDivisorHom K F).hom d ∈ T K U.obj := by
  apply imageSieve_mem_of_pointwise (affineDivisorHom K F).hom d
  intro x
  let B := coordinateRing K U.obj
  letI := coordinateAlgebra K U.obj
  letI := coordinateAlgebra_etale K U.obj
  letI : IsDomain B := U.property
  let e := coordinateChartIso K U.obj U.property
  let d' := (D K).map e.hom.op d
  obtain ⟨b, hb, u, hu⟩ := chartDivisorMap_localLift K B F x d'
  let C := Localization.Away b
  letI : IsDomain C := Localization.Away.isDomain (fun h ↦ hb (h.symm ▸ x.asIdeal.zero_mem))
  letI : Algebra.Etale B C := Algebra.Etale.of_isLocalizationAway b
  let a := chartArrow K B C
  let f := a ≫ e.hom
  let u₀ := (G K F).map e.inv.op u
  let m := (affineDivisorHom K F).hom
  have hApp : m.app (op U.obj) =
      (G K F).map e.hom.op ≫ AddCommGrpCat.ofHom (chartDivisorMap K B F) ≫
        (D K).map e.inv.op :=
    affineDivisorHom_app_integral K F U
  have hSource : (G K F).map e.inv.op ≫ (G K F).map e.hom.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id]
    exact (G K F).map_id _
  have hTarget : (D K).map e.inv.op ≫ (D K).map f.op = (D K).map a.op := by
    have hF : f ≫ e.inv = a := by
      change (a ≫ e.hom) ≫ e.inv = a
      rw [Category.assoc, e.hom_inv_id]
      exact Category.comp_id a
    rw [← Functor.map_comp, ← op_comp, hF]
  have hTarget' : (D K).map f.op = (D K).map e.hom.op ≫ (D K).map a.op := by
    rw [← Functor.map_comp, ← op_comp]
  refine ⟨chartObject K C, f, ?_, ?_⟩
  · refine ⟨(G K F).map f.op u₀, ?_⟩
    rw [NatTrans.naturality_apply, hApp]
    change (D K).map f.op ((D K).map e.inv.op
      (chartDivisorMap K B F ((G K F).map e.hom.op ((G K F).map e.inv.op u)))) =
      (D K).map f.op d
    have h₁ : (G K F).map e.hom.op ((G K F).map e.inv.op u) = u :=
      ConcreteCategory.congr_hom hSource u
    have h₂ : (D K).map f.op ((D K).map e.inv.op (chartDivisorMap K B F u)) =
        (D K).map a.op (chartDivisorMap K B F u) :=
      ConcreteCategory.congr_hom hTarget (chartDivisorMap K B F u)
    rw [h₁, h₂]
    exact hu.trans (ConcreteCategory.congr_hom hTarget' d).symm
  · let S := Scheme.AffineEtale.Spec (X K)
    have hS : (S.map f).left = Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [show f = a ≫ e.hom from rfl, S.map_comp]
      have hA : S.map a = algebraEtaleMap (IsScalarTower.toAlgHom (A K) B C) :=
        S.map_preimage _
      rw [hA]
      change Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (𝟙 (coordinateRing K U.obj)) = _
      rw [Spec.map_id]
      exact Category.comp_id (Spec.map (CommRingCat.ofHom (algebraMap B C)))
    rw [hS]
    have hx : (show PrimeSpectrum B from x) ∈ Set.range (PrimeSpectrum.comap (algebraMap B C)) := by
      rw [PrimeSpectrum.localization_away_comap_range C b]
      exact hb
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (Spec.map_apply (CommRingCat.ofHom (algebraMap B C)) y).trans hy⟩

/-- The actual affine étale divisor morphism is an epimorphism. -/
theorem affineDivisorHom_epi : Epi (affineDivisorHom K F) := by
  letI : (I K).IsCoverDense (T K) :=
    AffineEtaleDomainSite.integralCharts_coverDense (A K)
  letI : Sheaf.IsLocallySurjective (affineDivisorHom K F) :=
    of_coverDense (T K) (affineDivisorHom K F).hom (I K)
      (integralImageSieve_mem K F)
  infer_instance

/-- The actual divisor morphism on the full small étale site is epic. -/
theorem divisorHom_epi : Epi (divisorHom K F) := by
  letI : Epi (affineDivisorHom K F) := affineDivisorHom_epi K F
  unfold divisorHom
  infer_instance

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisorHom_epi,
      ``ManuscriptAudit.AffineLineDivisorSheaf.divisorHom_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
