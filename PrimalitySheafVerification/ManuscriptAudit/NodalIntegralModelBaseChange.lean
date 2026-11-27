import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluingOverlap
import PrimalitySheafVerification.ManuscriptAudit.NodalOverlapCoefficientMap

/-! Coefficient extension of the glued nodal curve is base change of the
actual scheme, by checking the two affine charts and their overlap. -/

namespace ManuscriptAudit.NodalIntegralModelBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing NodalIntegralGluingOverlap NodalChartCoefficientMaps
open NodalOverlapCoefficientMap
open PlaneEquationBaseChange (changeBase)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def chartMap : ∀ b : Bool, chartObj S b ⟶ chartObj R b
  | false => zMap R S
  | true => yMap R S

theorem overlapIn_natural (b : Bool) :
    overlapMap R S ≫ overlapIn R b = overlapIn S b ≫ chartMap R S b := by
  cases b
  · exact overlapToZ_natural R S
  · exact overlapToY_natural R S

theorem overlapIn_chartIn (T : Type u) [CommRing T] (b : Bool) :
    overlapIn T b ≫ chartIn T b = colimit.ι (diagram T) none :=
  colimit.w (diagram T) (WidePushoutShape.Hom.init b)

private def changedCocone : Cocone (diagram S) :=
  WidePushoutShape.mkCocone
    (overlapMap R S ≫ colimit.ι (diagram R) none)
    (fun b => chartMap R S b ≫ chartIn R b)
    (fun b => by rw [← Category.assoc, ← overlapIn_natural, Category.assoc, overlapIn_chartIn])

/-- The morphism induced by extension of coefficients on the two charts. -/
def modelMap : model S ⟶ model R := colimit.desc (diagram S) (changedCocone R S)

theorem chartIn_modelMap (b : Bool) :
    chartIn S b ≫ modelMap R S = chartMap R S b ≫ chartIn R b :=
  colimit.ι_desc (changedCocone R S) (some b)

private theorem chart_square (b : Bool) :
    IsPullback (chartToBase S b) (chartMap R S b)
      (changeBase R S) (chartToBase R b) := by
  cases b
  · exact zSquare_isPullback R S
  · exact ySquare_isPullback R S

private theorem overlap_y_square :
    IsPullback (overlapToY S) (overlapMap R S) (yMap R S) (overlapToY R) := by
  have h := (overlap_square_isPullback R S).paste_horiz (chart_square R S false)
  change IsPullback (overlapToZ S ≫ chartToBase S false) (overlapMap R S)
    (changeBase R S) (overlapToZ R ≫ chartToBase R false) at h
  rw [overlapToZ_over, overlapToZ_over, ← overlapToY_over S, ← overlapToY_over R] at h
  exact h.of_right (overlapToY_natural R S).symm (chart_square R S true)

private theorem range_of_square {A B X Y : Scheme.{u}} {i : A ⟶ X} {g : A ⟶ B}
    {f : X ⟶ Y} {j : B ⟶ Y} [IsOpenImmersion j] (h : IsPullback i g f j) :
    Set.range i = f ⁻¹' Set.range j := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst f j) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.homeomorph.surjective,
    Set.image_univ, IsOpenImmersion.range_pullbackFst] <;> rfl

private theorem overlap_range_in_source (b : Bool) :
    Set.range (overlapIn S b) = (chartMap R S b) ⁻¹' Set.range (overlapIn R b) := by
  cases b
  · exact range_of_square (overlap_square_isPullback R S)
  · exact range_of_square (overlap_y_square R S)

private theorem overlap_range_in_target (b c : Bool) (h : b ≠ c) :
    Set.range (overlapIn R b) = (chartIn R b) ⁻¹' Set.range (chartIn R c) := by
  cases b <;> cases c
  · exact (h rfl).elim
  · exact range_of_square (overlap_isPullback R)
  · exact range_of_square (overlap_isPullback R).flip
  · exact (h rfl).elim

private theorem chart_point_map (b : Bool) (q : chartObj S b) :
    modelMap R S (chartIn S b q) = chartIn R b (chartMap R S b q) := by
  rw [← Scheme.Hom.comp_apply, chartIn_modelMap, Scheme.Hom.comp_apply]

private theorem chart_range_preimage (b : Bool) :
    (modelMap R S) ⁻¹ᵁ (chartIn R b).opensRange = (chartIn S b).opensRange := by
  ext p
  change modelMap R S p ∈ Set.range (chartIn R b) ↔ p ∈ Set.range (chartIn S b)
  constructor
  · intro h
    have hCover : ∃ c : Bool, ∃ q : chartObj S c, chartIn S c q = p := by
      rcases charts_cover S p with ⟨q, hq⟩ | ⟨q, hq⟩
      · exact ⟨false, q, hq⟩
      · exact ⟨true, q, hq⟩
    obtain ⟨c, q, hq⟩ := hCover
    by_cases hc : c = b
    · subst c
      exact ⟨q, hq⟩
    · have hy : chartMap R S c q ∈ Set.range (overlapIn R c) := by
        rw [overlap_range_in_target R c b hc]
        change chartIn R c (chartMap R S c q) ∈ Set.range (chartIn R b)
        rw [← chart_point_map, hq]
        exact h
      have hx : q ∈ Set.range (overlapIn S c) := by
        rw [overlap_range_in_source]
        exact hy
      obtain ⟨r, hr⟩ := hx
      refine ⟨overlapIn S b r, ?_⟩
      rw [← Scheme.Hom.comp_apply, overlapIn_chartIn,
        ← overlapIn_chartIn S c, Scheme.Hom.comp_apply, hr, hq]
  · rintro ⟨p, rfl⟩
    exact ⟨chartMap R S b p, (chart_point_map R S b p).symm⟩

private theorem model_chart_square (b : Bool) :
    IsPullback (chartIn S b) (chartMap R S b) (modelMap R S) (chartIn R b) :=
  (IsOpenImmersion.isPullback (chartMap R S b) (chartIn S b) (chartIn R b) (modelMap R S)
    (chartIn_modelMap R S b) (chart_range_preimage R S b)).flip

private def twoChartCover (T : Type u) [CommRing T] : (model T).OpenCover where
  I₀ := Bool
  X := chartObj T
  f := chartIn T
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro p
    rcases charts_cover T p with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact ⟨false, q, hq⟩
    · exact ⟨true, q, hq⟩

/-- Base change for the actual whole nodal scheme, including the infinity chart. -/
theorem model_square_isPullback :
    IsPullback (toBase S) (modelMap R S) (changeBase R S) (toBase R) := by
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover _ _ _ _ (twoChartCover R)
  intro b
  change IsPullback (pullback.snd (modelMap R S) (chartIn R b))
    (pullback.fst (modelMap R S) (chartIn R b) ≫ toBase S)
    (chartIn R b ≫ toBase R) (changeBase R S)
  have hs := model_chart_square R S b
  exact (chart_square R S b).flip.of_iso hs.isoPullback (.refl _) (.refl _) (.refl _)
    (by simp [hs.isoPullback_hom_snd])
    (by simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
      hs.isoPullback_hom_fst, chartIn_over])
    (by simp [chartIn_over])
    (by simp)

end
end ManuscriptAudit.NodalIntegralModelBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalIntegralModelBaseChange.chartIn_modelMap,
      ``ManuscriptAudit.NodalIntegralModelBaseChange.model_square_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
