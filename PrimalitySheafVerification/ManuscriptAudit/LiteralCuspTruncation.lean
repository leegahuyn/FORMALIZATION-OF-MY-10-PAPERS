import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The literal height cutoff on the level-two modular quotient

Paper 10, physical p. 496, presents the quotient of the single height
sublevel as a cusp truncation. Every orbit already meets every positive
height sublevel. Thus the image of that sublevel is the entire quotient.
The sublevel itself is also unstable under the group action at every
positive cutoff height.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace ManuscriptAudit.LiteralCuspTruncation

abbrev GammaTwo : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma 2
abbrev OrbitQuotient := Quotient (MulAction.orbitRel GammaTwo ℍ)

private def lowerMatrix (n : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; 2 * n, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem lowerMatrix_mem (n : ℤ) : lowerMatrix n ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  change (1 : ZMod 2) = 1 ∧ (0 : ZMod 2) = 0 ∧
    ((2 * n : ℤ) : ZMod 2) = 0 ∧ (1 : ZMod 2) = 1
  simp [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide]

private def lowerElement (n : ℤ) : GammaTwo := ⟨lowerMatrix n, lowerMatrix_mem n⟩

private theorem lower_denom (n : ℤ) (z : ℍ) :
    UpperHalfPlane.denom (SpecialLinearGroup.toGL
      ((SpecialLinearGroup.map (Int.castRingHom ℝ)) (lowerMatrix n))) (z : ℂ) =
      2 * (n : ℂ) * (z : ℂ) + 1 := by
  rw [ModularGroup.denom_apply]
  norm_num [lowerMatrix, Int.cast_mul, mul_assoc]

/-- A lower unipotent in the actual congruence subgroup sends any representative
into the literal height sublevel at any positive cutoff. -/
theorem exists_smul_im_lt (Y : ℝ) (hY : 0 < Y) (z : ℍ) :
    ∃ g : GammaTwo, (g • z).im < Y := by
  let y := z.im
  have hy : 0 < y := z.2
  have hScale : 0 < 4 * Y * y := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (1 / (4 * Y * y)))
  have hn₁ : 1 < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnProd : 1 < (n : ℝ) * (4 * Y * y) :=
    (div_lt_iff₀ hScale).mp ((le_max_right _ _).trans_lt hn)
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hBig : 1 < (n : ℝ) ^ 2 * (4 * Y * y) :=
    hnProd.trans_le (mul_le_mul_of_nonneg_right hnSq hScale.le)
  have hMass : y < Y * (2 * (n : ℝ) * y) ^ 2 := by
    calc
      y = 1 * y := (one_mul _).symm
      _ < ((n : ℝ) ^ 2 * (4 * Y * y)) * y := mul_lt_mul_of_pos_right hBig hy
      _ = Y * (2 * (n : ℝ) * y) ^ 2 := by ring
  let d : ℂ := 2 * (n : ℂ) * (z : ℂ) + 1
  have hIm : d.im = 2 * (n : ℝ) * y := by
    simp [d, y, Complex.add_im, Complex.mul_im, Complex.mul_re]
  have hD : (2 * (n : ℝ) * y) ^ 2 ≤ Complex.normSq d := by
    rw [← hIm, Complex.normSq_apply]
    nlinarith [sq_nonneg d.re]
  have hBound : y < Y * Complex.normSq d :=
    hMass.trans_le (mul_le_mul_of_nonneg_left hD hY.le)
  have hdPos : 0 < Complex.normSq d := by
    by_contra! hNot
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hY.le hNot
    linarith
  refine ⟨lowerElement (n : ℤ), ?_⟩
  change (lowerMatrix (n : ℤ) • z).im < Y
  rw [ModularGroup.im_smul_eq_div_normSq, lower_denom]
  change y / Complex.normSq d < Y
  exact (div_lt_iff₀ hdPos).mpr hBound

def orbitPoint (z : ℍ) : OrbitQuotient := Quotient.mk _ z

/-- The image of the printed sublevel is the entire quotient. -/
theorem paper10_printed_sublevel_image_univ (Y : ℝ) (hY : 0 < Y) :
    orbitPoint '' {z : ℍ | z.im ≤ Y} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  obtain ⟨g, hg⟩ := exists_smul_im_lt Y hY z
  exact ⟨g • z, hg.le, Quotient.sound ⟨g, rfl⟩⟩

/-- No subset of the quotient pulls back to the printed sublevel. -/
theorem paper10_printed_sublevel_not_quotient_preimage (Y : ℝ) (hY : 0 < Y) :
    ¬ ∃ S : Set OrbitQuotient, ∀ z : ℍ, z.im ≤ Y ↔ orbitPoint z ∈ S := by
  rintro ⟨S, hS⟩
  let z : ℍ := ⟨⟨0, Y + 1⟩, by change 0 < Y + 1; linarith⟩
  obtain ⟨g, hg⟩ := exists_smul_im_lt Y hY z
  have hClass : orbitPoint (g • z) = orbitPoint z := Quotient.sound ⟨g, rfl⟩
  have hHigh := (hS z).mpr (hClass ▸ (hS (g • z)).mp hg.le)
  change Y + 1 ≤ Y at hHigh
  linarith

end ManuscriptAudit.LiteralCuspTruncation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LiteralCuspTruncation.exists_smul_im_lt,
      ``ManuscriptAudit.LiteralCuspTruncation.paper10_printed_sublevel_image_univ,
      ``ManuscriptAudit.LiteralCuspTruncation.paper10_printed_sublevel_not_quotient_preimage] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
