import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluingOverlap
import PrimalitySheafVerification.ManuscriptAudit.NodalOverlapDiagonal
import PrimalitySheafVerification.ManuscriptAudit.TwoChartDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! The actual glued nodal family is separated over its coefficient
scheme. Its relative diagonal is closed on the products of its two
affine charts. -/

namespace ManuscriptAudit.NodalIntegralSeparated

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing NodalIntegralGluingOverlap
open TwoChartDiagonal (intersectionToProduct square_isPullback)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

private def chartCover : (model R).OpenCover where
  I₀ := Bool
  X := chartObj R
  f := chartIn R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro p
    rcases charts_cover R p with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact ⟨false, q, hq⟩
    · exact ⟨true, q, hq⟩

private theorem same_chart_closed (b : Bool) :
    IsClosedImmersion (intersectionToProduct (toBase R) (chartIn R b) (chartIn R b)) := by
  let f := chartIn R b
  have h : pullback.fst f f = pullback.snd f f :=
    (cancel_mono f).mp pullback.condition
  have hD : intersectionToProduct (toBase R) f f =
      pullback.fst f f ≫ pullback.diagonal (f ≫ toBase R) := by
    apply pullback.hom_ext
    · simp [intersectionToProduct]
    · simpa [intersectionToProduct] using h.symm
  letI : IsIso (pullback.fst f f) :=
    (IsPullback.of_hasPullback f f).isIso_fst_of_mono
  letI : IsSeparated (f ≫ toBase R) := by
    change IsSeparated (chartIn R b ≫ toBase R)
    rw [chartIn_over]
    cases b
    · change IsSeparated (Spec.map _)
      infer_instance
    · change IsSeparated (Spec.map _)
      infer_instance
  change IsClosedImmersion (intersectionToProduct (toBase R) f f)
  rw [hD]
  infer_instance

private theorem cross_forward_closed :
    IsClosedImmersion
      (intersectionToProduct (toBase R) (chartIn R false) (chartIn R true)) := by
  let h := overlap_isPullback R
  let e := h.isoPullback
  have hz : e.hom ≫ pullback.fst (chartIn R false) (chartIn R true) = overlapToZ R :=
    h.isoPullback_hom_fst
  have hy : e.hom ≫ pullback.snd (chartIn R false) (chartIn R true) = overlapToY R :=
    h.isoPullback_hom_snd
  let hZ := chartIn_over R false
  let hY := chartIn_over R true
  let p := pullback.congrHom hZ hY
  have hD : e.hom ≫ intersectionToProduct (toBase R) (chartIn R false) (chartIn R true) ≫
      p.hom = NodalOverlapDiagonal.toProduct R := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
        Category.comp_id, intersectionToProduct, NodalOverlapDiagonal.toProduct]
      exact hz
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id, intersectionToProduct, NodalOverlapDiagonal.toProduct]
      exact hy
  have hD' : intersectionToProduct (toBase R) (chartIn R false) (chartIn R true) =
      e.inv ≫ NodalOverlapDiagonal.toProduct R ≫ p.inv := by
    rw [← hD]
    simp
  rw [hD']
  letI := NodalOverlapDiagonal.cross_chart_isClosedImmersion R
  infer_instance

private theorem cross_reverse_closed :
    IsClosedImmersion
      (intersectionToProduct (toBase R) (chartIn R true) (chartIn R false)) := by
  let f := chartIn R false
  let g := chartIn R true
  have hD : intersectionToProduct (toBase R) g f = (pullbackSymmetry g f).hom ≫
      intersectionToProduct (toBase R) f g ≫
        (pullbackSymmetry (f ≫ toBase R) (g ≫ toBase R)).hom := by
    apply pullback.hom_ext <;> simp [intersectionToProduct]
  change IsClosedImmersion (intersectionToProduct (toBase R) g f)
  rw [hD]
  letI : IsClosedImmersion (intersectionToProduct (toBase R) f g) := cross_forward_closed R
  infer_instance

private theorem all_product_charts (b c : Bool) :
    IsClosedImmersion (intersectionToProduct (toBase R) (chartIn R b) (chartIn R c)) := by
  cases b <;> cases c
  · exact same_chart_closed R false
  · exact cross_forward_closed R
  · exact cross_reverse_closed R
  · exact same_chart_closed R true

/-- Separatedness of the actual flat glued nodal family. -/
theorem model_isSeparated : IsSeparated (toBase R) := by
  constructor
  let cov := Scheme.Pullback.openCoverOfLeftRight (chartCover R) (chartCover R)
    (toBase R) (toBase R)
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) cov).mpr
  intro pair
  obtain ⟨b, c⟩ := pair
  let h := (square_isPullback (toBase R) (chartIn R b) (chartIn R c)).flip
  change IsClosedImmersion (pullback.snd (pullback.diagonal (toBase R))
    (TwoChartDiagonal.productChart (toBase R) (chartIn R b) (chartIn R c)))
  rw [← h.isoPullback_inv_snd]
  letI := all_product_charts R b c
  infer_instance

end
end ManuscriptAudit.NodalIntegralSeparated

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalIntegralSeparated.model_isSeparated
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
