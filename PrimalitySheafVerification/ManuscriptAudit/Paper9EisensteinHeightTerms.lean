import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# The literal height terms of the Eisenstein series on the level-two quotient

Paper 9, physical page 420, §3.2 identifies the full weight-zero
Eisenstein series with its two height terms. At s = 2 these terms are
y² + c/y. Every level-two orbit contains three representatives of
distinct positive heights. Equal values at two given heights force an
explicit coefficient, and the two smaller heights force different
coefficients. The calculation concerns the literal full-function
formula. A horocycle constant term is a different function of height.
-/

namespace ManuscriptAudit.Paper9EisensteinHeightTerms

open LiteralCuspTruncation
open scoped UpperHalfPlane

noncomputable section

/-- The literal two powers in the printed formula, using complex powers. -/
def printedHeightTerms (s c : ℂ) (z : ℍ) : ℂ :=
  (z.im : ℂ) ^ s + c * (z.im : ℂ) ^ (1 - s)

theorem printedHeightTerms_at_two (c : ℂ) (z : ℍ) :
    printedHeightTerms 2 c z = (z.im : ℂ) ^ 2 + c / (z.im : ℂ) := by
  rw [printedHeightTerms, show (1 : ℂ) - 2 = -1 by norm_num,
    Complex.cpow_ofNat, Complex.cpow_neg_one, div_eq_mul_inv]

private theorem coefficient_for_equal_heights {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) (c : ℂ)
    (h : (a : ℂ) ^ 2 + c / (a : ℂ) = (b : ℂ) ^ 2 + c / (b : ℂ)) :
    c = ((a * b * (a + b) : ℝ) : ℂ) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hDiff : (a : ℂ) - (b : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hab.ne'
  have haDiv : c / (a : ℂ) * ((a : ℂ) * (b : ℂ)) = c * (b : ℂ) := by
    rw [← mul_assoc, div_mul_cancel₀ _ haC]
  have hbDiv : c / (b : ℂ) * ((a : ℂ) * (b : ℂ)) = c * (a : ℂ) := by
    rw [mul_comm (a : ℂ) (b : ℂ), ← mul_assoc, div_mul_cancel₀ _ hbC]
  have hScaled := congrArg (fun v : ℂ => v * ((a : ℂ) * (b : ℂ))) h
  change ((a : ℂ) ^ 2 + c / (a : ℂ)) * ((a : ℂ) * (b : ℂ)) =
    ((b : ℂ) ^ 2 + c / (b : ℂ)) * ((a : ℂ) * (b : ℂ)) at hScaled
  rw [add_mul, add_mul, haDiv, hbDiv] at hScaled
  have hZero : ((a : ℂ) - (b : ℂ)) *
      (c - (a : ℂ) * (b : ℂ) * ((a : ℂ) + (b : ℂ))) = 0 := by
    linear_combination -hScaled
  simpa only [Complex.ofReal_mul, Complex.ofReal_add] using
    sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_left hDiff)

/-- The two printed height terms vary within every actual level-two orbit. -/
theorem every_orbit_has_different_printed_height_terms (c : ℂ) (z : ℍ) :
    ∃ w : ℍ, orbitPoint w = orbitPoint z ∧
      printedHeightTerms 2 c w ≠ printedHeightTerms 2 c z := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_im_lt z.im z.im_pos z
  let w₁ := g₁ • z
  have h₁ : w₁.im < z.im := hg₁
  by_cases hEq₁ : printedHeightTerms 2 c w₁ = printedHeightTerms 2 c z
  · obtain ⟨g₂, hg₂⟩ := exists_smul_im_lt w₁.im w₁.im_pos z
    let w₂ := g₂ • z
    have h₂ : w₂.im < w₁.im := hg₂
    refine ⟨w₂, Quotient.sound ⟨g₂, rfl⟩, ?_⟩
    intro hEq₂
    have hc₁ := coefficient_for_equal_heights z.im_pos w₁.im_pos h₁ c
      (by simpa only [printedHeightTerms_at_two] using hEq₁.symm)
    have hc₂ := coefficient_for_equal_heights z.im_pos w₂.im_pos (h₂.trans h₁) c
      (by simpa only [printedHeightTerms_at_two] using hEq₂.symm)
    have hReal : z.im * w₁.im * (z.im + w₁.im) =
        z.im * w₂.im * (z.im + w₂.im) := by
      exact_mod_cast hc₁.symm.trans hc₂
    have hStrict : z.im * w₂.im * (z.im + w₂.im) <
        z.im * w₁.im * (z.im + w₁.im) := by
      calc
        _ < z.im * w₁.im * (z.im + w₂.im) :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h₂ z.im_pos)
            (add_pos z.im_pos w₂.im_pos)
        _ < _ := mul_lt_mul_of_pos_left (add_lt_add_left h₂ _)
          (mul_pos z.im_pos w₁.im_pos)
    exact (ne_of_gt hStrict) hReal
  · exact ⟨w₁, Quotient.sound ⟨g₁, rfl⟩, hEq₁⟩

/-- At s = 2 no coefficient rescues the printed formula on the quotient. -/
theorem printed_height_terms_do_not_descend (c : ℂ) :
    ¬ ∃ E : OrbitQuotient → ℂ, ∀ z : ℍ, E (orbitPoint z) = printedHeightTerms 2 c z := by
  rintro ⟨E, hE⟩
  let z : ℍ := ⟨Complex.I, by simp⟩
  obtain ⟨w, hw, hd⟩ := every_orbit_has_different_printed_height_terms c z
  apply hd
  calc
    _ = E (orbitPoint w) := (hE w).symm
    _ = E (orbitPoint z) := congrArg E hw
    _ = _ := hE z

/-- The full-function identification in §3.2 fails in its stated
half-plane of definitions. -/
theorem printed_full_eisenstein_formula_refuted (φ : ℂ → ℂ) :
    ¬ ∃ E : OrbitQuotient → ℂ → ℂ,
      ∀ (z : ℍ) (s : ℂ), 1 < s.re → E (orbitPoint z) s = printedHeightTerms s (φ s) z := by
  rintro ⟨E, hE⟩
  exact printed_height_terms_do_not_descend (φ 2)
    ⟨fun w => E w 2, fun z => hE z 2 (by norm_num)⟩

end

end ManuscriptAudit.Paper9EisensteinHeightTerms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9EisensteinHeightTerms.printedHeightTerms_at_two,
      ``ManuscriptAudit.Paper9EisensteinHeightTerms.every_orbit_has_different_printed_height_terms,
      ``ManuscriptAudit.Paper9EisensteinHeightTerms.printed_height_terms_do_not_descend,
      ``ManuscriptAudit.Paper9EisensteinHeightTerms.printed_full_eisenstein_formula_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
