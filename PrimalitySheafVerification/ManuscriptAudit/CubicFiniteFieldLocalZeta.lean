import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteFieldPointRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualAnalyticLocalZeta

/-! Formal and convergent local zeta identities from the actual projective counts over every finite base. -/

namespace ManuscriptAudit.CubicFiniteFieldLocalZeta

open FiniteFieldPointCount CubicSplitExtensionTraceRecurrence CubicFiniteFieldPointRecurrence
open Paper5ActualHasseWeil Paper5ExtensionRecurrence EllipticQuadraticRadius
open PointCountExponential LocalTraceExponential PowerSeries

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] [CharP E p]

theorem point_count_cast (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (α β : ℂ)
    (ha : α + β = (signedTrace A : ℂ)) (hm : α * β = (Fintype.card E : ℂ)) (n : ℕ) :
    (pointCount p E A n : ℂ) =
      (Fintype.card E : ℂ) ^ (n+1) + 1 - α ^ (n+1) - β ^ (n+1) := by
  have h := congrArg (fun x : ℤ => (x : ℂ)) (pointCount_eq_recurrence p E hp hA n)
  push_cast at h
  rw [recurrence_cast_eq_root_powers (Fintype.card E) (signedTrace A) α β ha hm] at h
  linear_combination h

def pointCountSeries (A : E) : ℂ⟦X⟧ :=
  PowerSeries.X * PowerSeries.mk (fun n => (pointCount p E A n : ℂ))

/-- The literal formal exponential agrees with the genus-one Euler expression. -/
theorem formal_local_zeta (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (α β : ℂ)
    (ha : α + β = (signedTrace A : ℂ)) (hm : α * β = (Fintype.card E : ℂ)) :
    zetaOfCountSeries (pointCountSeries p E A) =
      (linearFactor α * linearFactor β) * (geometric 1 * geometric (Fintype.card E : ℂ)) := by
  have h : pointCountSeries p E A = twoRootCounts (Fintype.card E : ℂ) α β := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp only [pointCountSeries, twoRootCounts, coeff_zero_X_mul]
    | succ n =>
      simp only [pointCountSeries, twoRootCounts, coeff_succ_X_mul, coeff_mk]
      exact point_count_cast p E hp hA α β ha hm n
  rw [h, twoRootCounts_zeta]

private theorem reciprocal_root_norm (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) {α β : ℂ}
    (hs : α + β = (signedTrace A : ℂ)) (hm : α * β = (Fintype.card E : ℂ)) :
    ‖α‖ = Real.sqrt (Fintype.card E : ℝ) := by
  have hα : α ≠ 0 := by
    intro hz
    have he : (Fintype.card E : ℂ) = 0 := by simpa [hz] using hm.symm
    exact (Nat.cast_ne_zero.mpr (Fintype.card_pos : 0 < Fintype.card E).ne') he
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂ : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₂p
  have h₃ : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₃p
  have hChar : ringChar E ≠ 2 := by rw [ringChar.eq E p]; omega
  have hDiscr := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA
  let q := Fintype.card E
  let a := (q : ℝ) + 1 - (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℝ)
  have ha : (a : ℂ) = (signedTrace A : ℂ) := by
    dsimp [a, q, signedTrace]
    push_cast <;> rfl
  have hRoot : (localPolynomial (q : ℝ) a).IsRoot α⁻¹ := by
    rw [Polynomial.IsRoot, eval_localPolynomial]
    change 1 - (a : ℂ) * α⁻¹ + ((q : ℝ) : ℂ) * (α⁻¹)^2 = 0
    rw [ha, ← hs, Complex.ofReal_natCast]
    change 1 - (α + β) * α⁻¹ + (Fintype.card E : ℂ) * (α⁻¹)^2 = 0
    rw [← hm]
    field_simp [hα] <;> ring
  have h := Paper5ActualEulerRadius.actual_finite_cubic_roots_on_circle E hChar hA hDiscr α⁻¹ hRoot
  rw [norm_inv, one_div] at h
  exact inv_injective h

theorem exists_actual_roots (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) :
    ∃ α β : ℂ, α + β = (signedTrace A : ℂ) ∧ α * β = (Fintype.card E : ℂ) ∧
      ‖α‖ = Real.sqrt (Fintype.card E : ℝ) ∧ ‖β‖ = Real.sqrt (Fintype.card E : ℝ) := by
  obtain ⟨α, β, hs, hm⟩ := exist_two_roots (signedTrace A : ℂ) (Fintype.card E : ℂ)
  exact ⟨α, β, hs, hm, reciprocal_root_norm p E hp hA hs hm,
    reciprocal_root_norm p E hp hA (by rwa [add_comm]) (by rwa [mul_comm])⟩

def pointTerm (A : E) (z : ℂ) (n : ℕ) : ℂ :=
  (pointCount p E A n : ℂ) * z^(n+1) / ((n+1 : ℕ) : ℂ)

/-- The local zeta made from the actual extension-field point counts converges to the stated rational expression. -/
theorem actual_local_zeta (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) {z : ℂ}
    (hz : ‖z‖ < 1 / (Fintype.card E : ℝ)) :
    Summable (fun n : ℕ => ‖pointTerm p E A z n‖) ∧
      Complex.exp (∑' n : ℕ, pointTerm p E A z n) =
        (1 - (signedTrace A : ℂ) * z + (Fintype.card E : ℂ) * z^2) /
          ((1-z) * (1-(Fintype.card E : ℂ)*z)) := by
  obtain ⟨α, β, ha, hm, hα, hβ⟩ := exists_actual_roots p E hp hA
  let q := Fintype.card E
  have hq : 0 < q := Fintype.card_pos
  have hpR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp₁ : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from hq)
  have hpz : (q : ℝ) * ‖z‖ < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hpR).mp hz
  have hz₁ : ‖z‖ < 1 := (le_mul_of_one_le_left (norm_nonneg z) hp₁).trans_lt hpz
  have hpCz : ‖(q : ℂ) * z‖ < 1 := by
    simpa only [norm_mul, Complex.norm_natCast] using hpz
  have hS : Real.sqrt q ≤ q := (Real.sqrt_le_self_iff).mpr (Or.inr hp₁)
  have hαz : ‖α * z‖ < 1 := by
    rw [norm_mul, hα]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hpz
  have hβz : ‖β * z‖ < 1 := by
    rw [norm_mul, hβ]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hpz
  have hTerm (n : ℕ) : pointTerm p E A z n =
      term n ((q : ℂ)*z) + term n z - term n (α*z) - term n (β*z) := by
    unfold pointTerm
    rw [point_count_cast p E hp hA α β ha hm n]
    simp only [term, mul_pow]
    ring
  have hAbs := (((term_norm_summable hpCz).add (term_norm_summable hz₁)).add
    (term_norm_summable hαz)).add (term_norm_summable hβz)
  have hSum : HasSum (pointTerm p E A z)
      (traceLog ((q : ℂ)*z) + traceLog z - traceLog (α*z) - traceLog (β*z)) := by
    have h := (((traceLog_hasSum hpCz).add (traceLog_hasSum hz₁)).sub
      (traceLog_hasSum hαz)).sub (traceLog_hasSum hβz)
    have he : (fun n : ℕ => term n ((q : ℂ)*z) + term n z -
        term n (α*z) - term n (β*z)) = pointTerm p E A z :=
      funext (fun n => (hTerm n).symm)
    rw [he] at h
    simpa only [traceLog, (traceLog_hasSum hpCz).tsum_eq, (traceLog_hasSum hz₁).tsum_eq,
      (traceLog_hasSum hαz).tsum_eq, (traceLog_hasSum hβz).tsum_eq] using h
  constructor
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hAbs
    intro n
    rw [hTerm]
    calc
      _ ≤ ‖term n ((q : ℂ)*z) + term n z - term n (α*z)‖ + ‖term n (β*z)‖ :=
        norm_sub_le _ _
      _ ≤ (‖term n ((q : ℂ)*z) + term n z‖ + ‖term n (α*z)‖) + ‖term n (β*z)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
  · rw [hSum.tsum_eq, Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
      exp_traceLog hpCz, exp_traceLog hz₁, exp_traceLog hαz, exp_traceLog hβz]
    have hFactor : (1-α*z)*(1-β*z) = 1 - (signedTrace A : ℂ)*z + (q : ℂ)*z^2 := by
      linear_combination -z*ha + z^2*hm
    rw [← hFactor]
    have hNZ (w : ℂ) (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
      intro h
      have he : (1 : ℂ) = w := sub_eq_zero.mp h
      simpa only [← he, norm_one, lt_irrefl] using hw
    field_simp [hNZ _ hpCz, hNZ _ hz₁, hNZ _ hαz, hNZ _ hβz] <;> ring

end
end ManuscriptAudit.CubicFiniteFieldLocalZeta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFiniteFieldLocalZeta.point_count_cast,
      ``ManuscriptAudit.CubicFiniteFieldLocalZeta.formal_local_zeta,
      ``ManuscriptAudit.CubicFiniteFieldLocalZeta.exists_actual_roots,
      ``ManuscriptAudit.CubicFiniteFieldLocalZeta.actual_local_zeta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
