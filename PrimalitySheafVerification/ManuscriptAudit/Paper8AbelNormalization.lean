import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic

/-! A summation-by-parts criterion for an ordinary weighted series. -/

namespace ManuscriptAudit.Paper8AbelNormalization

open Filter Asymptotics
open scoped Topology

noncomputable section

theorem normalized_partial_sums_tendsto_zero (a : ℕ → ℝ) (g : ℕ → ℂ)
    (haPos : ∀ n, 0 < a n) (haMono : Monotone a) (ha : Tendsto a atTop atTop)
    {L : ℂ} (hG : Tendsto (fun n => ∑ i ∈ Finset.range n, g i) atTop (𝓝 L)) :
    Tendsto (fun n => (a n)⁻¹ • ∑ i ∈ Finset.range (n + 1), a i • g i) atTop (𝓝 0) := by
  let G (n : ℕ) := ∑ i ∈ Finset.range n, g i
  let Δ (n : ℕ) := a (n + 1) - a n
  let F (n : ℕ) := Δ n • (G (n + 1) - L)
  have hd (n : ℕ) : 0 ≤ Δ n := sub_nonneg.mpr (haMono (Nat.le_succ n))
  have hTel (n : ℕ) : (∑ i ∈ Finset.range n, Δ i) = a n - a 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; unfold Δ; ring
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun n hn => ?_
    exact hn.trans (Nat.le_succ n)
  have hSmall : Tendsto (fun n : ℕ => G (n + 1) - L) atTop (𝓝 0) := by
    have hShifted : Tendsto (fun n => G (n + 1)) atTop (𝓝 L) := hG.comp hShift
    have hL : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := tendsto_const_nhds
    simpa only [sub_self] using hShifted.sub hL
  have hF : F =o[atTop] Δ := by
    refine isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hSmall ε hε] with n hn
    rw [dist_zero_right] at hn
    change ‖Δ n • (G (n + 1) - L)‖ ≤ ε * ‖Δ n‖
    rw [norm_smul, Real.norm_of_nonneg (hd n)]
    simpa only [mul_comm ε] using mul_le_mul_of_nonneg_left hn.le (hd n)
  have hTelLim : Tendsto (fun n => ∑ i ∈ Finset.range n, Δ i) atTop atTop := by
    refine tendsto_atTop.2 fun c => ?_
    filter_upwards [tendsto_atTop.1 ha (c + a 0)] with n hn
    rw [hTel]
    linarith
  have hTelBound : (fun n => ∑ i ∈ Finset.range n, Δ i) =O[atTop] a := by
    refine isBigO_iff.2 ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
    have hNonneg : 0 ≤ a n - a 0 := sub_nonneg.mpr (haMono (Nat.zero_le n))
    rw [hTel, Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg (haPos n).le, one_mul]
    linarith [haPos 0]
  have hSum := (hF.sum_range hd hTelLim).trans_isBigO hTelBound
  have hDiv : (fun n => (a n)⁻¹ • ∑ i ∈ Finset.range n, F i) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    apply ((isBigO_refl (fun n => (a n)⁻¹) atTop).smul_isLittleO hSum).congr'
      Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun n => by
      change (a n)⁻¹ • a n = 1
      rw [smul_eq_mul, inv_mul_cancel₀ (haPos n).ne']
  have hDivLim := (isLittleO_one_iff ℝ).1 hDiv
  have hHead : Tendsto (fun n => (a n)⁻¹ • (a 0 • L)) atTop (𝓝 0) := by
    have hi : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ha
    simpa only [zero_smul] using hi.smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a 0 • L) atTop (𝓝 (a 0 • L)))
  have hLim : Tendsto (fun n => (G (n + 1) - L) -
      (a n)⁻¹ • (∑ i ∈ Finset.range n, F i) + (a n)⁻¹ • (a 0 • L)) atTop (𝓝 0) := by
    simpa only [sub_zero, zero_add] using (hSmall.sub hDivLim).add hHead
  apply hLim.congr
  intro n
  have hSplit : (∑ i ∈ Finset.range n, Δ i • G (i + 1)) =
      (∑ i ∈ Finset.range n, F i) + (a n - a 0) • L := by
    rw [← hTel n, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold F
    rw [← smul_add, sub_add_cancel]
  have hParts := Finset.sum_range_by_parts a g (n + 1)
  simp only [Nat.add_sub_cancel] at hParts
  change (∑ i ∈ Finset.range (n + 1), a i • g i) =
    a n • G (n + 1) - ∑ i ∈ Finset.range n, Δ i • G (i + 1) at hParts
  simp only [hParts, hSplit, smul_sub, smul_add, sub_smul, smul_smul,
    inv_mul_cancel₀ (haPos n).ne', one_smul]
  abel

end
end ManuscriptAudit.Paper8AbelNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8AbelNormalization.normalized_partial_sums_tendsto_zero
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
