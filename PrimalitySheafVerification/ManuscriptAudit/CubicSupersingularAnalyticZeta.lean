import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularCanonicalZeta
import PrimalitySheafVerification.ManuscriptAudit.CubicHasseBound
import PrimalitySheafVerification.ManuscriptAudit.EllipticQuadraticRadius
import PrimalitySheafVerification.ManuscriptAudit.LocalTraceExponential

/-! The actual finite extension point counts give the analytic local zeta on its convergence disk. -/

namespace ManuscriptAudit.CubicSupersingularAnalyticZeta

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicSupersingularCanonicalZeta CubicSupersingularPointCountRecurrence
open EllipticQuadraticRadius LocalTraceExponential

noncomputable section

private theorem factor_norm (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h₂ : ringChar F ≠ 2) {A : F} (hA : A ≠ 0) (hΔ : (shortCubic (0 : F) A).Δ ≠ 0)
    {α β : ℂ} (hSum : α + β = (signedCount F A : ℂ))
    (hProd : α * β = (Fintype.card F : ℂ)) :
    ‖α‖ = Real.sqrt (Fintype.card F : ℝ) := by
  let q : ℝ := Fintype.card F
  let a : ℝ := signedCount F A
  have hq : 0 < q := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hqC : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hα : α ≠ 0 := by
    intro h
    exact hqC (hProd.symm.trans (by simp [h]))
  have hb : |a| ≤ 2 * Real.sqrt q := by
    simpa only [a, q, signedCount, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
      using CubicHasseBound.reducedCubic_hasse h₂ hA hΔ
  have hαRoot : (localPolynomial q a).IsRoot α⁻¹ := by
    change (localPolynomial q a).eval α⁻¹ = 0
    rw [eval_localPolynomial]
    change 1 - (a : ℂ) * α⁻¹ + (q : ℂ) * (α⁻¹) ^ 2 = 0
    have hs : (a : ℂ) = α + β := by simpa only [a, Complex.ofReal_intCast] using hSum.symm
    have hp : (q : ℂ) = α * β := by simpa only [q, Complex.ofReal_natCast] using hProd.symm
    rw [hs, hp]
    field_simp [hα] <;> ring
  have hRadius := (all_roots_radius_iff q a hq).mpr hb α⁻¹ hαRoot
  have hInv := congrArg (fun t : ℝ => t⁻¹) hRadius
  simpa only [q, norm_inv, inv_inv, one_div] using hInv

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] [CharP F p]

/-- The degree-(n+1) contribution of the literal point count to the analytic exponent. -/
def pointTerm (A : F) (z : ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff (n + 1) (actualCounts p F A) * z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

theorem actual_zeta_eq (hp : 5 ≤ p) (hP : p % 3 = 2) {A : F} (hA : A ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1 / (Fintype.card F : ℝ)) :
    Summable (pointTerm p F A z) ∧
      Complex.exp (∑' n : ℕ, pointTerm p F A z n) =
        (1 - (signedCount F A : ℂ) * z + (Fintype.card F : ℂ) * z ^ 2) /
          ((1 - z) * (1 - (Fintype.card F : ℂ) * z)) := by
  obtain ⟨α, β, ha, hm⟩ :=
    Paper5ActualHasseWeil.exist_two_roots (signedCount F A : ℂ) (Fintype.card F : ℂ)
  let q : ℝ := Fintype.card F
  let qC : ℂ := Fintype.card F
  have hq : 0 < q := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hq₁ : 1 ≤ q := by exact_mod_cast (le_of_lt (Fintype.one_lt_card : 1 < Fintype.card F))
  have h₂ : ringChar F ≠ 2 := by rw [ringChar.eq F p]; omega
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂F : (2 : F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₂p
  have h₃F : (3 : F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₃p
  have hΔ := shortCubic_discriminant_ne_zero h₂F h₃F hA
  have hα := factor_norm F h₂ hA hΔ ha hm
  have hβ := factor_norm F h₂ hA hΔ ((add_comm β α).trans ha) ((mul_comm β α).trans hm)
  have hqz : q * ‖z‖ < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hq).mp hz
  have hz₁ : ‖z‖ < 1 :=
    (le_mul_of_one_le_left (norm_nonneg z) hq₁).trans_lt hqz
  have hqCz : ‖qC * z‖ < 1 := by
    simpa only [qC, q, norm_mul, Complex.norm_natCast] using hqz
  have hS : Real.sqrt q ≤ q := (Real.sqrt_le_self_iff).mpr (Or.inr hq₁)
  have hαz : ‖α * z‖ < 1 := by
    rw [norm_mul, hα]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hqz
  have hβz : ‖β * z‖ < 1 := by
    rw [norm_mul, hβ]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hqz
  have hTerm (n : ℕ) : pointTerm p F A z n =
      term n (qC * z) + term n z - term n (α * z) - term n (β * z) := by
    unfold pointTerm
    rw [count_coefficient_eq p F hp hP hA ha hm]
    unfold term qC
    simp only [mul_pow]
    ring
  have hHas : HasSum (pointTerm p F A z)
      (traceLog (qC * z) + traceLog z - traceLog (α * z) - traceLog (β * z)) := by
    have h := (((traceLog_hasSum hqCz).add (traceLog_hasSum hz₁)).sub
      (traceLog_hasSum hαz)).sub (traceLog_hasSum hβz)
    exact h.congr (fun n => (hTerm n).symm)
  refine ⟨hHas.summable, ?_⟩
  rw [hHas.tsum_eq, Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
    exp_traceLog hqCz, exp_traceLog hz₁, exp_traceLog hαz, exp_traceLog hβz]
  have hf : (1 - α * z) * (1 - β * z) =
      1 - (signedCount F A : ℂ) * z + qC * z ^ 2 := by
    change (1 - α * z) * (1 - β * z) =
      1 - (signedCount F A : ℂ) * z + (Fintype.card F : ℂ) * z ^ 2
    linear_combination -z * ha + z ^ 2 * hm
  change (1 - qC * z)⁻¹ * (1 - z)⁻¹ / (1 - α * z)⁻¹ / (1 - β * z)⁻¹ =
    (1 - (signedCount F A : ℂ) * z + qC * z ^ 2) / ((1 - z) * (1 - qC * z))
  rw [← hf]
  have hNZ (w : ℂ) (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
    intro hz
    have he : (1 : ℂ) = w := sub_eq_zero.mp hz
    simpa only [← he, norm_one, lt_irrefl] using hw
  field_simp [hNZ _ hqCz, hNZ _ hz₁, hNZ _ hαz, hNZ _ hβz] <;> ring

end
end ManuscriptAudit.CubicSupersingularAnalyticZeta

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularAnalyticZeta.actual_zeta_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
