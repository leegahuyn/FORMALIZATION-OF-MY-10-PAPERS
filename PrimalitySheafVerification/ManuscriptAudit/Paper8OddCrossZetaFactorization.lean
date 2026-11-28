import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareRowKernel

/-! Arithmetic zeta factor of the first cross-cusp Fourier kernel and convergence in its initial half-plane. -/

namespace ManuscriptAudit.Paper8OddCrossZetaFactorization

open Paper8OddCrossCuspCutoff Paper8OddCrossCuspRows Paper8OddCrossPoincareKernel
open Paper8OddCrossScaledRows Paper8OddCrossPoincareRowKernel MaassLaplacian
open Paper8DedekindZeroReference (referenceZeroSum)
open Paper8ContourResidueWeights (dedekindSum)

noncomputable section

def crossModulusFactor (s : ℂ) (c : ℝ) : ℂ := (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ s

def crossLeadingKernel (s : ℂ) (y u : ℝ) : ℂ :=
  (starRingEnd ℂ) (normalizedNegativeRoot (complexPoint u y)) *
    ((y / (u ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s *
    exponentialPhase (-(oddZeroFrequency : ℂ) * (u : ℂ))

def crossRemainderKernel (s : ℂ) (y c u : ℝ) : ℂ :=
  crossLeadingKernel s y u *
    (exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * complexPoint u y)) - 1)

theorem crossRealKernel_factor (s : ℂ) {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (u : ℝ) :
    crossRealKernel s y c u =
      crossModulusFactor s c * (crossLeadingKernel s y u + crossRemainderKernel s y c u) := by
  have hH : y / (c ^ 2 * (u ^ 2 + y ^ 2)) = (c ^ 2)⁻¹ * (y / (u ^ 2 + y ^ 2)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  let w := complexPoint u y
  let a := -(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * w)
  let b := (oddZeroFrequency : ℂ) * (u : ℂ)
  have hEx : exponentialPhase (a - b) = exponentialPhase a * exponentialPhase (-b) := by
    unfold exponentialPhase
    rw [sub_eq_add_neg, mul_add, Complex.exp_add]
  unfold crossRealKernel crossModulusFactor crossRemainderKernel crossLeadingKernel
  try dsimp only
  rw [hH, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), hEx]
  simp only [neg_mul]
  change _ = _ * (((starRingEnd ℂ) (normalizedNegativeRoot w) *
      ((y / (u ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s * exponentialPhase (-b)) +
    ((starRingEnd ℂ) (normalizedNegativeRoot w) *
      ((y / (u ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s * exponentialPhase (-b)) * (exponentialPhase a - 1))
  ring

theorem norm_crossSum_le {D : ℕ} (hD : 0 < D) : ‖crossSum hD‖ ≤ (D : ℝ) := by
  have hC : ‖(chiFour (D : ZMod 4) : ℂ)‖ ≤ 1 := by
    unfold chiFour
    split_ifs <;> norm_num
  rw [crossSum_eq hD, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hC).trans ?_
  unfold referenceZeroSum
  apply (norm_sum_le _ _).trans
  have hU (d : Fin D) : ‖Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((dedekindSum (d.val : ℤ) D : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, Complex.mul_im]
  simp only [hU, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hCard : ((Finset.univ : Finset (Fin D)).filter (fun d => Nat.Coprime d.val D)).card ≤ D :=
    (Finset.card_filter_le Finset.univ (fun d : Fin D => Nat.Coprime d.val D)).trans (by simp)
  exact_mod_cast hCard

theorem crossModulusFactor_norm (s : ℂ) {c : ℝ} (hc : 0 < c) :
    ‖crossModulusFactor s c‖ = c ^ (-2 * s.re) := by
  rw [crossModulusFactor, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Real.inv_rpow (sq_nonneg c), ← Real.rpow_natCast_mul hc.le 2 s.re]
  rw [show (((2 : ℕ) : ℝ) * s.re) = 2 * s.re by norm_num,
    show (-2 * s.re : ℝ) = -(2 * s.re) by ring, Real.rpow_neg hc.le]

def oddCrossZetaTerm (s : ℂ) (D : ℕ) : ℂ :=
  crossSum (Nat.succ_pos D) * crossModulusFactor s (2 * ((D + 1 : ℕ) : ℝ))

theorem norm_oddCrossZetaTerm_le (s : ℂ) (D : ℕ) :
    ‖oddCrossZetaTerm s D‖ ≤
      (2 : ℝ) ^ (-2 * s.re) * ((D : ℝ) + 1) ^ (1 - 2 * s.re) := by
  have hD : 0 < ((D + 1 : ℕ) : ℝ) := by positivity
  rw [oddCrossZetaTerm, norm_mul, crossModulusFactor_norm s (by positivity),
    Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hD.le]
  calc
    _ ≤ ((D + 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-2 * s.re) * ((D + 1 : ℕ) : ℝ) ^ (-2 * s.re)) :=
      mul_le_mul_of_nonneg_right (norm_crossSum_le (Nat.succ_pos D)) (by positivity)
    _ = _ := by
      push_cast
      rw [show (1 - 2 * s.re : ℝ) = 1 + (-2 * s.re) by ring, Real.rpow_add (by positivity), Real.rpow_one]
      ring

theorem oddCrossZetaTerm_abs_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun D : ℕ => ‖oddCrossZetaTerm s D‖) := by
  have h : Summable (fun D : ℕ => ((D : ℝ) + 1) ^ (1 - 2 * s.re)) :=
    ((Real.summable_one_div_nat_add_rpow 1 (2 * s.re - 1)).2 (by linarith)).congr (fun D => by
      rw [abs_of_nonneg (by positivity : 0 ≤ (D : ℝ) + 1), one_div,
        ← Real.rpow_neg (by positivity : 0 ≤ (D : ℝ) + 1)]
      congr 1
      ring)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_oddCrossZetaTerm_le s) (h.mul_left _)

end
end ManuscriptAudit.Paper8OddCrossZetaFactorization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossZetaFactorization.crossRealKernel_factor,
      ``ManuscriptAudit.Paper8OddCrossZetaFactorization.oddCrossZetaTerm_abs_summable] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
