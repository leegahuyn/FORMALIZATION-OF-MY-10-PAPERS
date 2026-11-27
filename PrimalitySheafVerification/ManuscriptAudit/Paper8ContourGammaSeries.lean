import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convergence of the literal aₖ(s) in physical p. 335, §5.2.4

The exponent of π/(12k) is 2m + 1/2. Gamma recurrence gives a
uniformly summable majorant on each positive lower bound for ‖s‖.
This verifies the individual Laurent series on its punctured domain.
-/

namespace ManuscriptAudit.Paper8ContourGammaSeries

open Filter Set
open scoped Topology

noncomputable section

def scale (k : ℕ) : ℝ := Real.pi / (12 * (k : ℝ))

def coefficient (k m : ℕ) : ℝ :=
  scale k ^ (2 * (m : ℝ) + 1 / 2) / Real.Gamma ((m : ℝ) + 3 / 2)

def term (k m : ℕ) (s : ℂ) : ℂ := (coefficient k m : ℂ) / s ^ (m + 1)

def a (k : ℕ) (s : ℂ) : ℂ := ∑' m : ℕ, term k m s

private theorem scale_pos {k : ℕ} (hk : 0 < k) : 0 < scale k := by
  unfold scale
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact div_pos Real.pi_pos (mul_pos (by norm_num) hkR)

private theorem gamma_argument_pos (m : ℕ) : 0 < (m : ℝ) + 3 / 2 := by positivity

theorem coefficient_pos {k : ℕ} (hk : 0 < k) (m : ℕ) : 0 < coefficient k m :=
  div_pos (Real.rpow_pos_of_pos (scale_pos hk) _) (Real.Gamma_pos_of_pos (gamma_argument_pos m))

theorem coefficient_succ {k : ℕ} (hk : 0 < k) (m : ℕ) :
    coefficient k (m + 1) = (scale k ^ 2 / ((m : ℝ) + 3 / 2)) * coefficient k m := by
  have hExponent : 2 * ((m + 1 : ℕ) : ℝ) + 1 / 2 = (2 * (m : ℝ) + 1 / 2) + 2 := by
    push_cast
    ring
  have hArgument : ((m + 1 : ℕ) : ℝ) + 3 / 2 = ((m : ℝ) + 3 / 2) + 1 := by
    push_cast
    ring
  have hPos := gamma_argument_pos m
  unfold coefficient
  rw [hExponent, hArgument, Real.rpow_add (scale_pos hk), Real.rpow_two, Real.Gamma_add_one hPos.ne']
  field_simp [hPos.ne', (Real.Gamma_pos_of_pos hPos).ne'] <;> ring

def majorant (k : ℕ) (r : ℝ) (m : ℕ) : ℝ := coefficient k m / r ^ (m + 1)

private theorem majorant_pos {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    0 < majorant k r m :=
  div_pos (coefficient_pos hk m) (pow_pos hr _)

private theorem majorant_succ {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    majorant k r (m + 1) =
      (scale k ^ 2 / (r * ((m : ℝ) + 3 / 2))) * majorant k r m := by
  unfold majorant
  rw [coefficient_succ hk, pow_succ' r (m + 1)]
  field_simp [hr.ne', (gamma_argument_pos m).ne', pow_ne_zero _ hr.ne'] <;> ring

theorem majorant_summable {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    Summable (majorant k r) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * scale k ^ 2 / r)
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  rw [Real.norm_of_nonneg (majorant_pos hk hr (m + 1)).le,
    Real.norm_of_nonneg (majorant_pos hk hr m).le, majorant_succ hk hr]
  refine mul_le_mul_of_nonneg_right ?_ (majorant_pos hk hr m).le
  apply (div_le_iff₀ (mul_pos hr (gamma_argument_pos m))).2
  have hmR : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hBound : 2 * scale k ^ 2 < (m : ℝ) * r :=
    ((div_lt_iff₀ hr).1 hN).trans_le (mul_le_mul_of_nonneg_right hmR hr.le)
  nlinarith [mul_nonneg hr.le (by norm_num : (0 : ℝ) ≤ 3 / 2)]

theorem norm_term_le_majorant {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : r ≤ ‖s‖) (m : ℕ) : ‖term k m s‖ ≤ majorant k r m := by
  rw [term, majorant, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (coefficient_pos hk m).le]
  exact div_le_div_of_nonneg_left (coefficient_pos hk m).le (pow_pos hr _)
    (pow_le_pow_left₀ hr.le hs _)

theorem absolute_summable {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : s ≠ 0) :
    Summable (fun m => ‖term k m s‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_majorant hk
    (norm_pos_iff.mpr hs) le_rfl) (majorant_summable hk (norm_pos_iff.mpr hs))

theorem hasSumUniformlyOn_of_lower_norm {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    HasSumUniformlyOn (term k) (a k) {s : ℂ | r ≤ ‖s‖} :=
  HasSumUniformlyOn.of_norm_le_summable (f := term k) (majorant_summable hk hr)
    (fun m _ hs => norm_term_le_majorant hk hr hs m)

theorem hasSumLocallyUniformlyOn_punctured {k : ℕ} (hk : 0 < k) :
    HasSumLocallyUniformlyOn (term k) (a k) {s : ℂ | s ≠ 0} := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  let r : ℝ := ‖s‖ / 2
  have hNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hr : 0 < r := half_pos hNorm
  have hOpen : IsOpen {z : ℂ | r < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hsR : s ∈ {z : ℂ | r < ‖z‖} := by
    change ‖s‖ / 2 < ‖s‖
    linarith
  have hSub : {z : ℂ | r < ‖z‖} ⊆ {z : ℂ | r ≤ ‖z‖} := by
    intro z hz
    change r ≤ ‖z‖
    exact (show r < ‖z‖ from hz).le
  exact ⟨{z : ℂ | r < ‖z‖}, mem_nhdsWithin_of_mem_nhds (hOpen.mem_nhds hsR),
    (hasSumUniformlyOn_of_lower_norm hk hr).mono hSub⟩

theorem differentiableOn_punctured {k : ℕ} (hk : 0 < k) :
    DifferentiableOn ℂ (a k) {s : ℂ | s ≠ 0} := by
  intro s hs
  let r : ℝ := ‖s‖ / 2
  have hNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hr : 0 < r := half_pos hNorm
  let U : Set ℂ := {z : ℂ | r < ‖z‖}
  have hOpen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hsU : s ∈ U := by
    change ‖s‖ / 2 < ‖s‖
    linarith
  have hTerm (m : ℕ) : DifferentiableOn ℂ (term k m) U := by
    intro z hz
    have hzNorm : r < ‖z‖ := hz
    have hz₀ : z ≠ 0 := norm_pos_iff.mp (hr.trans hzNorm)
    have hConst : DifferentiableAt ℂ (fun _ : ℂ => (coefficient k m : ℂ)) z :=
      differentiableAt_const (c := (coefficient k m : ℂ))
    have hPow : DifferentiableAt ℂ (fun w : ℂ => w ^ (m + 1)) z :=
      differentiableAt_id.pow (m + 1)
    exact (hConst.div hPow (pow_ne_zero _ hz₀)).differentiableWithinAt
  have hDiff : DifferentiableOn ℂ (a k) U :=
    Complex.differentiableOn_tsum_of_summable_norm (F := term k) (majorant_summable hk hr)
      hTerm hOpen (fun m _ hz => norm_term_le_majorant hk hr (le_of_lt hz) m)
  exact ((hDiff s hsU).differentiableAt (hOpen.mem_nhds hsU)).differentiableWithinAt

end
end ManuscriptAudit.Paper8ContourGammaSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourGammaSeries.coefficient_pos,
      ``ManuscriptAudit.Paper8ContourGammaSeries.coefficient_succ,
      ``ManuscriptAudit.Paper8ContourGammaSeries.majorant_summable,
      ``ManuscriptAudit.Paper8ContourGammaSeries.norm_term_le_majorant,
      ``ManuscriptAudit.Paper8ContourGammaSeries.absolute_summable,
      ``ManuscriptAudit.Paper8ContourGammaSeries.hasSumUniformlyOn_of_lower_norm,
      ``ManuscriptAudit.Paper8ContourGammaSeries.hasSumLocallyUniformlyOn_punctured,
      ``ManuscriptAudit.Paper8ContourGammaSeries.differentiableOn_punctured] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
