import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# Orbit comparison in the high infinity cusp of the level-two quotient

Paper 10, physical PDF p. 496. For points of imaginary part above `Y ≥ 1`,
the only equivalences under the actual level-two congruence group are even
horizontal integer translations. This gives one representative with real
part in `[0, 2)` for each orbit through that high strip.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace ManuscriptAudit.HighInfinityCusp

open LiteralCuspTruncation (GammaTwo orbitPoint)

private theorem int_sq_ge_one {c : ℤ} (hc : c ≠ 0) : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
  have hcases : c ≤ -1 ∨ 1 ≤ c := by omega
  rcases hcases with h | h
  · have hr : (c : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith only [mul_nonneg (show 0 ≤ -(c : ℝ) - 1 by linarith)
      (show 0 ≤ 1 - (c : ℝ) by linarith)]
  · have hr : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
    nlinarith only [mul_nonneg (show 0 ≤ (c : ℝ) - 1 by linarith)
      (show 0 ≤ (c : ℝ) + 1 by linarith)]

theorem height_le_of_bottom_left_ne_zero (g : SL(2, ℤ)) (z : ℍ) (hc : g 1 0 ≠ 0) :
    (g • z).im ≤ 1 / (((g 1 0 : ℤ) : ℝ) ^ 2 * z.im) := by
  let G : GL (Fin 2) ℝ := g
  let d := Complex.normSq (UpperHalfPlane.denom G (z : ℂ))
  have hd : 0 < d := UpperHalfPlane.normSq_denom_pos G z.im_ne_zero
  have hdenom : (((g 1 0 : ℤ) : ℝ) * z.im) ^ 2 ≤ d :=
    UpperHalfPlane.c_mul_im_sq_le_normSq_denom G z
  have hcsq : (1 : ℝ) ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 := int_sq_ge_one hc
  have hE : 0 < ((g 1 0 : ℤ) : ℝ) ^ 2 * z.im :=
    mul_pos (lt_of_lt_of_le zero_lt_one hcsq) z.im_pos
  rw [ModularGroup.im_smul_eq_div_normSq]
  change z.im / d ≤ 1 / (((g 1 0 : ℤ) : ℝ) ^ 2 * z.im)
  apply (div_le_div_iff₀ hd hE).mpr
  calc
    z.im * (((g 1 0 : ℤ) : ℝ) ^ 2 * z.im) = (((g 1 0 : ℤ) : ℝ) * z.im) ^ 2 := by ring
    _ ≤ 1 * d := by simpa only [one_mul] using hdenom

theorem height_lt_one_of_bottom_left_ne_zero (g : SL(2, ℤ)) (z : ℍ)
    (hz : 1 < z.im) (hc : g 1 0 ≠ 0) : (g • z).im < 1 := by
  have hcsq := int_sq_ge_one hc
  have hE : 1 < ((g 1 0 : ℤ) : ℝ) ^ 2 * z.im := by
    calc
      (1 : ℝ) < z.im := hz
      _ = 1 * z.im := (one_mul _).symm
      _ ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 * z.im := mul_le_mul_of_nonneg_right hcsq z.im_pos.le
  refine (height_le_of_bottom_left_ne_zero g z hc).trans_lt ?_
  exact (div_lt_iff₀ (zero_lt_one.trans hE)).2 (by simpa only [one_mul] using hE)

theorem bottom_left_zero_of_high_image {Y : ℝ} (hY : 1 ≤ Y) (g : SL(2, ℤ))
    {z : ℍ} (hz : Y < z.im) (hgz : Y < (g • z).im) : g 1 0 = 0 := by
  by_contra hc
  exact (not_lt_of_ge hY) (hgz.trans
    (height_lt_one_of_bottom_left_ne_zero g z (hY.trans_lt hz) hc))

private theorem sl_smul_coe (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + (g 0 1 : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℂ)) := by
  simpa using UpperHalfPlane.coe_specialLinearGroup_apply g z

private def translationMatrix (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 2 * m; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem translationMatrix_mem (m : ℤ) : translationMatrix m ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  change (1 : ZMod 2) = 1 ∧ ((2 * m : ℤ) : ZMod 2) = 0 ∧
    (0 : ZMod 2) = 0 ∧ (1 : ZMod 2) = 1
  simp [Int.cast_mul, show (2 : ZMod 2) = 0 by decide]

private def translation (m : ℤ) : GammaTwo := ⟨translationMatrix m, translationMatrix_mem m⟩

private theorem translation_smul_coe (m : ℤ) (z : ℍ) :
    ((translation m • z : ℍ) : ℂ) = (z : ℂ) + 2 * (m : ℂ) := by
  change ((translationMatrix m • z : ℍ) : ℂ) = _
  rw [sl_smul_coe]
  norm_num [translationMatrix, Int.cast_mul]

theorem even_translate_of_bottom_left_zero (g : GammaTwo) (z : ℍ)
    (hc : (g : SL(2, ℤ)) 1 0 = 0) :
    ∃ m : ℤ, ((g • z : ℍ) : ℂ) = (z : ℂ) + 2 * (m : ℂ) := by
  let s : SL(2, ℤ) := g
  have hc' : s 1 0 = 0 := hc
  have hdet : s 0 0 * s 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc', mul_zero, sub_zero] using s.det_coe
  have hb : (s 0 1 : ZMod 2) = 0 := (CongruenceSubgroup.Gamma_mem.mp g.2).2.1
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (s 0 1) 2).mp hb
  have hsign := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet
  change ∃ m : ℤ, ((s • z : ℍ) : ℂ) = (z : ℂ) + 2 * (m : ℂ)
  rcases hsign with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · refine ⟨m, ?_⟩
    rw [sl_smul_coe, ha, hc', hd, hm]
    norm_num [Int.cast_mul]
  · refine ⟨-m, ?_⟩
    rw [sl_smul_coe, ha, hc', hd, hm]
    norm_num [Int.cast_mul] <;> ring

theorem high_orbit_iff_even_translate {Y : ℝ} (hY : 1 ≤ Y) {z w : ℍ}
    (hz : Y < z.im) (hw : Y < w.im) :
    (∃ g : GammaTwo, g • z = w) ↔
      ∃ m : ℤ, (w : ℂ) = (z : ℂ) + 2 * (m : ℂ) := by
  constructor
  · rintro ⟨g, hg⟩
    have hgz : Y < ((g : SL(2, ℤ)) • z).im := by
      change Y < (g • z).im
      rw [hg]
      exact hw
    obtain ⟨m, hm⟩ := even_translate_of_bottom_left_zero g z
      (bottom_left_zero_of_high_image hY (g : SL(2, ℤ)) hz hgz)
    exact ⟨m, hg ▸ hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨translation m, UpperHalfPlane.coe_inj.mp ((translation_smul_coe m z).trans hm.symm)⟩

theorem high_orbitPoint_eq_iff_even_translate {Y : ℝ} (hY : 1 ≤ Y) {z w : ℍ}
    (hz : Y < z.im) (hw : Y < w.im) :
    orbitPoint w = orbitPoint z ↔ ∃ m : ℤ, (w : ℂ) = (z : ℂ) + 2 * (m : ℂ) := by
  constructor
  · intro h
    exact (high_orbit_iff_even_translate hY hz hw).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((high_orbit_iff_even_translate hY hz hw).mpr h)

theorem existsUnique_high_strip_representative {Y : ℝ} (hY : 1 ≤ Y) (z : ℍ) (hz : Y < z.im) :
    ∃! w : ℍ, Y < w.im ∧ 0 ≤ w.re ∧ w.re < 2 ∧ orbitPoint w = orbitPoint z := by
  let m : ℤ := -⌊z.re / 2⌋
  let w : ℍ := translation m • z
  have hco : (w : ℂ) = (z : ℂ) + 2 * (m : ℂ) := translation_smul_coe m z
  have hRe : w.re = z.re + 2 * (m : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hco
  have hIm : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hco
  have hw : Y < w.im := hIm.symm ▸ hz
  have hflo := Int.floor_le (z.re / 2)
  have hfhi := Int.lt_floor_add_one (z.re / 2)
  have hwlo : 0 ≤ w.re := by rw [hRe]; simp only [m, Int.cast_neg]; linarith
  have hwhi : w.re < 2 := by rw [hRe]; simp only [m, Int.cast_neg]; linarith
  have hwOrb : orbitPoint w = orbitPoint z := Quotient.sound ⟨translation m, rfl⟩
  refine ⟨w, ⟨hw, hwlo, hwhi, hwOrb⟩, ?_⟩
  intro u hu
  obtain ⟨n, hn⟩ := (high_orbitPoint_eq_iff_even_translate hY hw hu.1).mp
    (hu.2.2.2.trans hwOrb.symm)
  have huRe : u.re = w.re + 2 * (n : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hn
  have hlo : (-1 : ℝ) < (n : ℝ) := by linarith only [huRe, hu.2.1, hwhi]
  have hhi : (n : ℝ) < 1 := by linarith only [huRe, hu.2.2.1, hwlo]
  have hloZ : (-1 : ℤ) < n := by exact_mod_cast hlo
  have hhiZ : n < (1 : ℤ) := by exact_mod_cast hhi
  have hn0 : n = 0 := by omega
  exact UpperHalfPlane.coe_inj.mp (by simpa [hn0] using hn)

end ManuscriptAudit.HighInfinityCusp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.HighInfinityCusp.height_le_of_bottom_left_ne_zero,
      ``ManuscriptAudit.HighInfinityCusp.bottom_left_zero_of_high_image,
      ``ManuscriptAudit.HighInfinityCusp.high_orbitPoint_eq_iff_even_translate,
      ``ManuscriptAudit.HighInfinityCusp.existsUnique_high_strip_representative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
