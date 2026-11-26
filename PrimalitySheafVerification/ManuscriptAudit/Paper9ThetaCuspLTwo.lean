import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9ThetaCuspPhases
import PrimalitySheafVerification.ManuscriptAudit.ThetaInfinityCusp

/-! Square integrability of the normalized theta profiles at all three cusps. -/

namespace ManuscriptAudit.Paper9ThetaCuspLTwo

open Paper9ThetaCuspPhases ThetaInfinityCusp MaassLaplacian MeasureTheory
open scoped UpperHalfPlane

noncomputable section

private def halfTerm (n : ℤ) (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)

private theorem thetaHalfShift_eq_tsum (τ : ℂ) :
    thetaHalfShift τ = ∑' n : ℤ, halfTerm n τ := by
  unfold thetaHalfShift jacobiTheta₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [jacobiTheta₂_term, halfTerm, ← Complex.exp_add]
  congr 1
  ring

private theorem norm_halfTerm (n : ℤ) (τ : ℂ) :
    ‖halfTerm n τ‖ = Real.exp (-Real.pi * (((n : ℝ) + 1 / 2) ^ 2) * τ.im) := by
  have h : (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ =
      (↑(Real.pi * (((n : ℝ) + 1 / 2) ^ 2)) : ℂ) * τ * Complex.I := by
    push_cast
    ring
  rw [halfTerm, h, Complex.norm_exp, Complex.mul_I_re, Complex.im_ofReal_mul]
  congr 1
  ring

private theorem integer_half_sq (n : ℤ) : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  have h : 0 ≤ ((n : ℝ) + 1) * (3 * (n : ℝ) + 1) := by
    by_cases hn : 0 ≤ n
    · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (by linarith) (by linarith)
    · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  nlinarith

private def halfBound (H : ℝ) :=
  ∑' n : ℤ, Real.exp (-Real.pi * (H / 4 * (n : ℝ) ^ 2))

private theorem norm_thetaHalfShift_le {H : ℝ} (hH : 0 < H) {τ : ℂ} (hτ : H ≤ τ.im) :
    ‖thetaHalfShift τ‖ ≤ halfBound H := by
  have hs : Summable (fun n : ℤ => Real.exp (-Real.pi * (H / 4 * (n : ℝ) ^ 2))) := by
    simpa only [pow_zero, one_mul, zero_mul, sub_zero] using
      (summable_pow_mul_jacobiTheta₂_term_bound 0 (T := H / 4) (by positivity) 0)
  have hd (n : ℤ) : ‖halfTerm n τ‖ ≤ Real.exp (-Real.pi * (H / 4 * (n : ℝ) ^ 2)) := by
    rw [norm_halfTerm]
    apply Real.exp_le_exp.mpr
    have hSq : H / 4 * (n : ℝ) ^ 2 ≤ (((n : ℝ) + 1 / 2) ^ 2) * τ.im := by
      calc
        _ = ((n : ℝ) ^ 2 / 4) * H := by ring
        _ ≤ ((n : ℝ) + 1 / 2) ^ 2 * H :=
          mul_le_mul_of_nonneg_right (integer_half_sq n) hH.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hτ (sq_nonneg _)
    simpa only [mul_assoc] using mul_le_mul_of_nonpos_left hSq (neg_nonpos.mpr Real.pi_pos.le)
  have hAbs : Summable (fun n : ℤ => ‖halfTerm n τ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hd hs
  rw [thetaHalfShift_eq_tsum]
  exact (norm_tsum_le_tsum_norm hAbs).trans (tsum_le_tsum hd hAbs hs)

theorem continuousAt_thetaHalfShift {τ : ℂ} (hτ : 0 < τ.im) : ContinuousAt thetaHalfShift τ := by
  have hExp : Continuous (fun z : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * z / 4)) :=
    Complex.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 4)
  have hArg : Continuous (fun z : ℂ => (z / 2, z)) :=
    (continuous_id.div_const 2).prodMk continuous_id
  exact hExp.continuousAt.mul ((continuousAt_jacobiTheta₂ (τ / 2) hτ).comp hArg.continuousAt)

theorem thetaHalfShift_memLp (H a : ℝ) (hH : 0 < H) (ha : a < 1 / 2) :
    MemLp (fun z : ℝ × ℝ => weighted a thetaHalfShift z.1 z.2) 2 (infinityCuspMeasureAbove H) := by
  refine weighted_memLp_of_bound thetaHalfShift H a (halfBound H) hH ha ?_ ?_
  · intro τ hτ
    exact continuousAt_thetaHalfShift hτ
  · intro x y hy
    exact norm_thetaHalfShift_le hH (by simpa only [complexPoint_im] using hy)

/-- The holomorphic-coordinate realizations of the actual normalized
profiles for the three fixed cusp charts. -/
def chartProfile (i : Fin 3) (τ : ℂ) : ℂ :=
  if i = 2 then thetaHalfShift τ else jacobiTheta τ

theorem chartProfile_eq (i : Fin 3) (z : ℍ) :
    chartProfile i z = normalizedProfile i z := by
  fin_cases i
  · simpa [chartProfile] using (normalizedProfile_zero z).symm
  · simpa [chartProfile] using (normalizedProfile_one z).symm
  · simpa [chartProfile] using (normalizedProfile_two z).symm

theorem normalizedProfile_norm_width_two (i : Fin 3) (z : ℍ) :
    ‖normalizedProfile i (ModularGroup.T ^ (2 : ℕ) • z)‖ = ‖normalizedProfile i z‖ := by
  have hp : ‖parabolicPhase i‖ = 1 := by fin_cases i <;> simp [parabolicPhase]
  rw [normalizedProfile_width_two, norm_mul, hp, one_mul]

theorem chartProfile_memLp (i : Fin 3) (H a : ℝ) (hH : 0 < H) (ha : a < 1 / 2) :
    MemLp (fun z : ℝ × ℝ => weighted a (chartProfile i) z.1 z.2) 2
      (infinityCuspMeasureAbove H) := by
  fin_cases i
  · simpa [chartProfile] using weighted_jacobiTheta_memLp_infinity_above H a hH ha
  · simpa [chartProfile] using weighted_jacobiTheta_memLp_infinity_above H a hH ha
  · simpa [chartProfile] using thetaHalfShift_memLp H a hH ha

theorem halfWeight_memLp_all_cusps (i : Fin 3) (H : ℝ) (hH : 0 < H) :
    MemLp (fun z : ℝ × ℝ => weighted (1 / 4) (chartProfile i) z.1 z.2) 2
      (infinityCuspMeasureAbove H) :=
  chartProfile_memLp i H (1 / 4) hH (by norm_num)

end
end ManuscriptAudit.Paper9ThetaCuspLTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.continuousAt_thetaHalfShift,
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.thetaHalfShift_memLp,
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.chartProfile_eq,
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.normalizedProfile_norm_width_two,
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.chartProfile_memLp,
      ``ManuscriptAudit.Paper9ThetaCuspLTwo.halfWeight_memLp_all_cusps] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
