import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaNormCusp

/-! The actual eta squared Petersson mass is invariant under integral modular translates. -/

namespace ManuscriptAudit.Paper8EtaPeterssonMass

open Set MeasureTheory UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8ActualEtaNormCusp
open scoped MatrixGroups ENNReal

noncomputable section

def density (z : ℍ) : ℝ≥0∞ := ENNReal.ofReal (‖ModularForm.eta z‖ ^ 2 * Real.sqrt z.im)

def mass (S : Set ℍ) : ℝ≥0∞ := ∫⁻ z in S, density z

def translate (g : SL(2, ℤ)) (S : Set ℍ) : Set ℍ := (fun z : ℍ => g • z) '' S

theorem density_smul (g : SL(2, ℤ)) (z : ℍ) : density (g • z) = density z := by
  have hD : 0 < ‖denominator g z‖ := norm_pos_iff.mpr (denominator_ne_zero g z)
  unfold density
  rw [eta_norm_square_transform, ModularGroup.im_smul_eq_div_normSq, ← denominator_eq,
    Complex.normSq_eq_norm_sq, Real.sqrt_div z.im_pos.le, Real.sqrt_sq hD.le]
  congr 1
  field_simp [hD.ne'] <;> ring

theorem mass_translate (g : SL(2, ℤ)) (S : Set ℍ) : mass (translate g S) = mass S := by
  have hMeasure : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  simpa only [mass, translate, density_smul] using (hMeasure.setLIntegral_comp_emb hEmb density S).symm

theorem mass_disjoint_translates {ι : Type*} [Fintype ι] (g : ι → SL(2, ℤ)) {S : Set ℍ}
    (hS : MeasurableSet S)
    (hDisj : Pairwise (fun i j => AEDisjoint (volume : Measure ℍ) (translate (g i) S) (translate (g j) S))) :
    mass (⋃ i : ι, translate (g i) S) = (Fintype.card ι : ℝ≥0∞) * mass S := by
  have hCells (i : ι) : NullMeasurableSet (translate (g i) S) (volume : Measure ℍ) := by
    have hEmb : MeasurableEmbedding (fun z : ℍ => g i • z) :=
      measurableEmbedding_const_smul (g i : GL (Fin 2) ℝ)
    exact (hEmb.measurableSet_image.mpr hS).nullMeasurableSet
  change (∫⁻ z in ⋃ i : ι, translate (g i) S, density z) = _
  rw [lintegral_iUnion₀ hCells hDisj]
  change (∑' i : ι, mass (translate (g i) S)) = _
  simp only [mass_translate, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end
end ManuscriptAudit.Paper8EtaPeterssonMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaPeterssonMass.density_smul,
      ``ManuscriptAudit.Paper8EtaPeterssonMass.mass_translate,
      ``ManuscriptAudit.Paper8EtaPeterssonMass.mass_disjoint_translates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
