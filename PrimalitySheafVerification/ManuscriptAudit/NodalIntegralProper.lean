import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import PrimalitySheafVerification.ManuscriptAudit.NodalValuationZLift
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralSeparated

/-! The actual glued nodal model satisfies the existence part of the
valuative criterion. Combining this with separatedness proves properness
over the coefficient ring, in particular over the integers. -/

namespace ManuscriptAudit.NodalIntegralProper

open AlgebraicGeometry CategoryTheory
open NodalIntegralChartTransition NodalIntegralGluing NodalIntegralGluingOverlap
open NodalValuationZLift

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

universe u
variable (R : Type u) [CommRing R]
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

private def yLocalized (f : yChart R →+* K) (hz : f (zY R) ≠ 0) :
    yOverlap R →+* K :=
  IsLocalization.Away.lift (g := f) (zY R) (isUnit_iff_ne_zero.mpr hz)

private theorem yLocalized_map (f : yChart R →+* K) (hz : f (zY R) ≠ 0) (a : yChart R) :
    yLocalized R f hz (algebraMap (yChart R) (yOverlap R) a) = f a :=
  IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr hz) _

private def yPointOverlap (f : yChart R →+* K) (hz : f (zY R) ≠ 0) :
    zOverlap R →+* K :=
  (yLocalized R f hz).comp (zToY R).toRingHom

private def yAsZ (f : yChart R →+* K) (hz : f (zY R) ≠ 0) :
    zChart R →+* K :=
  (yLocalized R f hz).comp (zInY R).toRingHom

private theorem yAsZ_coeff (f : yChart R →+* K) (hz : f (zY R) ≠ 0) (a : R) :
    yAsZ R f hz (algebraMap R (zChart R) a) = f (algebraMap R (yChart R) a) := by
  change yLocalized R f hz (zInY R (algebraMap R (zChart R) a)) = _
  rw [(zInY R).commutes, IsScalarTower.algebraMap_apply R (yChart R) (yOverlap R),
    yLocalized_map]

private theorem yAsZ_same_point (f : yChart R →+* K) (hz : f (zY R) ≠ 0) :
    Spec.map (CommRingCat.ofHom (yAsZ R f hz)) ≫ chartIn R false =
      Spec.map (CommRingCat.ofHom f) ≫ chartIn R true := by
  let p := Spec.map (CommRingCat.ofHom (yPointOverlap R f hz))
  have hZ : p ≫ overlapToZ R = Spec.map (CommRingCat.ofHom (yAsZ R f hz)) := by
    unfold p overlapToZ
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change yLocalized R f hz (zToY R (algebraMap (zChart R) (zOverlap R) a)) =
      yLocalized R f hz (zInY R a)
    rw [zToY_algebraMap]
  have hY : p ≫ overlapToY R = Spec.map (CommRingCat.ofHom f) := by
    change Spec.map (CommRingCat.ofHom (yPointOverlap R f hz)) ≫
      (Spec.map (CommRingCat.ofHom (yToZ R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (yChart R) (yOverlap R)))) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change yLocalized R f hz ((transition R) ((transition R).symm
      (algebraMap (yChart R) (yOverlap R) a))) = f a
    rw [AlgEquiv.apply_symm_apply, yLocalized_map]
  calc
    _ = p ≫ overlapToZ R ≫ chartIn R false := by rw [← Category.assoc, hZ]
    _ = p ≫ overlapToY R ≫ chartIn R true := by rw [overlap_condition]
    _ = _ := by rw [← Category.assoc, hY]

private theorem lift_yPoint (c : R →+* V) (f : yChart R →+* K)
    (hc : ∀ a : R, f (algebraMap R (yChart R) a) = algebraMap V K (c a)) :
    ∃ g : Spec (CommRingCat.of V) ⟶ model R,
      inFractionField ≫ g = Spec.map (CommRingCat.ofHom f) ≫ chartIn R true ∧
      g ≫ toBase R = Spec.map (CommRingCat.ofHom c) := by
  by_cases hz : f (zY R) = 0
  · have h := congrArg f (y_relation R)
    simp only [map_mul, map_pow, map_add, hz, add_zero] at h
    have hxpow : f (xY R) ^ 3 = 0 := by rw [pow_succ, ← h]
    have hx : f (xY R) = 0 := (pow_eq_zero hxpow)
    exact liftFromY R c f hc 0 0 (by rw [map_zero, hx]) (by rw [map_zero, hz]) (by ring)
  · obtain ⟨g, hg, hbase⟩ := lift_zPoint R c (yAsZ R f hz)
      (fun a => (yAsZ_coeff R f hz a).trans (hc a))
    exact ⟨g, hg.trans (yAsZ_same_point R f hz), hbase⟩

private theorem factor_through_chart {F : Type u} [Field F]
    (s : Spec (CommRingCat.of F) ⟶ model R) :
    ∃ (b : Bool) (t : Spec (CommRingCat.of F) ⟶ chartObj R b),
      t ≫ chartIn R b = s := by
  have hs : ∃ b : Bool, s (⊥ : PrimeSpectrum F) ∈ Set.range (chartIn R b) := by
    rcases charts_cover R (s (⊥ : PrimeSpectrum F)) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨b, hb⟩ := hs
  have hincl : Set.range s ⊆ Set.range (chartIn R b) := by
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (⊥ : PrimeSpectrum F)]
  exact ⟨b, IsOpenImmersion.lift (chartIn R b) s hincl,
    IsOpenImmersion.lift_fac _ _ _⟩

private theorem chart_spec_witness (S : ValuativeCommSq (toBase R)) (b : Bool)
    (F : CommRingCat.{u}) (f : F ⟶ CommRingCat.of S.K) (c : CommRingCat.of R ⟶ CommRingCat.of S.R)
    (k : CommRingCat.of R ⟶ F) (hs : Spec.map f ≫ chartIn R b = S.i₁)
    (hc : Spec.map c = S.i₂) (hk : Spec.map k = chartToBase R b) :
    k ≫ f = c ≫ CommRingCat.ofHom (algebraMap S.R S.K) := by
  apply Spec.map_inj
  rw [Spec.map_comp, Spec.map_comp, hc, hk, ← chartIn_over, ← Category.assoc, hs]
  exact S.commSq.w

/-- Actual scheme-theoretic existence, for every valuation square. -/
theorem valuative_existence : ValuativeCriterion.Existence (toBase R) := by
  intro S
  obtain ⟨b, g, hg⟩ := factor_through_chart R S.i₁
  obtain ⟨c, hc⟩ := Spec.map_surjective S.i₂
  cases b
  · change Spec (.of S.K) ⟶ zScheme R at g
    obtain ⟨f, hf⟩ := Spec.map_surjective g
    have hG : Spec.map f ≫ chartIn R false = S.i₁ := by rw [hf]; exact hg
    have hw : CommRingCat.ofHom (algebraMap R (zChart R)) ≫ f =
        c ≫ CommRingCat.ofHom (algebraMap S.R S.K) :=
      chart_spec_witness R S false _ f c _ hG hc rfl
    have hC (a : R) : f.hom (algebraMap R (zChart R) a) = algebraMap S.R S.K (c.hom a) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hw) a
    obtain ⟨l, hl, hl'⟩ := lift_zPoint R c.hom f.hom hC
    exact ⟨⟨⟨l, hl.trans hG, hl'.trans hc⟩⟩⟩
  · change Spec (.of S.K) ⟶ yScheme R at g
    obtain ⟨f, hf⟩ := Spec.map_surjective g
    have hG : Spec.map f ≫ chartIn R true = S.i₁ := by rw [hf]; exact hg
    have hw : CommRingCat.ofHom (algebraMap R (yChart R)) ≫ f =
        c ≫ CommRingCat.ofHom (algebraMap S.R S.K) :=
      chart_spec_witness R S true _ f c _ hG hc rfl
    have hC (a : R) : f.hom (algebraMap R (yChart R) a) = algebraMap S.R S.K (c.hom a) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hw) a
    obtain ⟨l, hl, hl'⟩ := lift_yPoint R c.hom f.hom hC
    exact ⟨⟨⟨l, hl.trans hG, hl'.trans hc⟩⟩⟩

/-- The flat finite-type glued nodal family over the coefficient ring is proper. -/
theorem model_proper : IsProper (toBase R) := by
  obtain ⟨hType, hComp⟩ := NodalIntegralGluing.model_finiteType R
  letI : LocallyOfFiniteType (toBase R) := hType
  letI : QuasiCompact (toBase R) := hComp
  letI : IsSeparated (toBase R) := NodalIntegralSeparated.model_isSeparated R
  letI : UniversallyClosed (toBase R) :=
    UniversallyClosed.of_valuativeCriterion _ (valuative_existence R)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end
end ManuscriptAudit.NodalIntegralProper

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalIntegralProper.valuative_existence,
      ``ManuscriptAudit.NodalIntegralProper.model_proper] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
