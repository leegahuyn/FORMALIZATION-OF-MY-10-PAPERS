import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindResidueMoments
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindTriangle

/-! Dedekind reciprocity for the manuscript's exact rational sawtooth sum. -/

namespace ManuscriptAudit.Paper8DedekindReciprocity

open Finset Paper8ContourResidueWeights Paper8DedekindResidueMoments Paper8DedekindTriangle

private theorem residue_fraction_sub {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) (j : Fin k) :
    fraction (residuePerm h k hk hC j) = (h : ℚ) * fraction j - (floorSlope h j : ℚ) := by
  have hN := Nat.mod_add_div (h * j.val) k
  have hQ := congrArg (fun n : ℕ => (n : ℚ)) hN
  push_cast at hQ
  have hK : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold fraction floorSlope
  rw [residuePerm_val]
  field_simp [hK] <;> nlinarith [hQ]

private theorem val_eq_mul_fraction {k : ℕ} (hk : 0 < k) (j : Fin k) :
    (j.val : ℚ) = (k : ℚ) * fraction j := by
  have hK : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold fraction
  field_simp [hK]

private theorem sum_vals {k : ℕ} (hk : 0 < k) :
    (∑ j : Fin k, (j.val : ℚ)) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
  simp_rw [val_eq_mul_fraction hk]
  rw [← Finset.mul_sum, sum_fraction hk]
  ring

private theorem floor_quadratic_from_residue {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) :
    (∑ j : Fin k, (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1)) =
      ((h : ℚ) ^ 2 + 1) * (∑ j : Fin k, fraction j ^ 2) -
        2 * (h : ℚ) * dedekindSum (h : ℤ) k - ((k : ℚ) - 1) / 2 := by
  let e := residuePerm h k hk hC
  have hy : (∑ j : Fin k, fraction (e j)) = ∑ j : Fin k, fraction j :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hy2 : (∑ j : Fin k, fraction (e j) ^ 2) = ∑ j : Fin k, fraction j ^ 2 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hP (j : Fin k) :
      (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1) =
        fraction (e j) ^ 2 + (h : ℚ) ^ 2 * fraction j ^ 2 -
          (2 * (h : ℚ)) * (fraction j * fraction (e j)) +
          (h : ℚ) * fraction j - fraction (e j) := by
    simp only [e, residue_fraction_sub hk hC]
    ring
  have hD := dedekindSum_eq_fraction_product hk hC
  change dedekindSum (h : ℤ) k =
    (∑ j : Fin k, fraction j * fraction (e j)) - ((k : ℚ) - 1) / 4 at hD
  simp_rw [hP]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hy, hy2, hD,
    sum_fraction hk]
  ring

private theorem weighted_floor_from_residue {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) :
    (∑ j : Fin k, (j.val : ℚ) * (floorSlope h j : ℚ)) =
      (k : ℚ) * ((h : ℚ) * (∑ j : Fin k, fraction j ^ 2) -
        dedekindSum (h : ℤ) k - ((k : ℚ) - 1) / 4) := by
  let e := residuePerm h k hk hC
  have hP (j : Fin k) : (j.val : ℚ) * (floorSlope h j : ℚ) =
      (k : ℚ) * ((h : ℚ) * fraction j ^ 2 - fraction j * fraction (e j)) := by
    rw [val_eq_mul_fraction hk]
    simp only [e, residue_fraction_sub hk hC]
    ring
  have hD := dedekindSum_eq_fraction_product hk hC
  change dedekindSum (h : ℤ) k =
    (∑ j : Fin k, fraction j * fraction (e j)) - ((k : ℚ) - 1) / 4 at hD
  simp_rw [hP]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hD]
  ring

private theorem triangle_to_weighted_floor {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) :
    (∑ j : Fin k, (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1)) =
      2 * (((k : ℚ) - 1) * (∑ v : Fin h, (v.val : ℚ)) -
        ∑ v : Fin h, (v.val : ℚ) * (floorSlope k v : ℚ)) := by
  have hCast (v : Fin h) : ((k - 1 - floorSlope k v : ℕ) : ℚ) =
      (k : ℚ) - 1 - (floorSlope k v : ℚ) := by
    have hV := floorSlope_lt hh v hk
    have hLe : floorSlope k v ≤ k - 1 := by omega
    rw [Nat.cast_sub hLe, Nat.cast_sub hk, Nat.cast_one]
  rw [floorSlope_quadratic_sum hh hk hC]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [hCast]
  ring

theorem dedekindSum_reciprocity_scaled {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) :
    (12 * (h : ℚ) * (k : ℚ)) * (dedekindSum (h : ℤ) k + dedekindSum (k : ℤ) h) =
      (h : ℚ) ^ 2 + (k : ℚ) ^ 2 - 3 * (h : ℚ) * (k : ℚ) + 1 := by
  let T := ∑ j : Fin k, (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1)
  have hH : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hK : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hFirst : 6 * (k : ℚ) * T =
      ((h : ℚ) ^ 2 + 1) * ((k : ℚ) - 1) * (2 * (k : ℚ) - 1) -
        12 * (h : ℚ) * (k : ℚ) * dedekindSum (h : ℤ) k -
          3 * (k : ℚ) * ((k : ℚ) - 1) := by
    rw [show T = _ from floor_quadratic_from_residue hk hC, sum_fraction_sq hk]
    field_simp [hK] <;> ring
  have hSecond : 6 * (k : ℚ) * T =
      6 * (k : ℚ) * ((k : ℚ) - 1) * (h : ℚ) * ((h : ℚ) - 1) -
        2 * (k : ℚ) ^ 2 * ((h : ℚ) - 1) * (2 * (h : ℚ) - 1) +
        12 * (k : ℚ) * (h : ℚ) * dedekindSum (k : ℤ) h +
        3 * (k : ℚ) * (h : ℚ) * ((h : ℚ) - 1) := by
    rw [show T = _ from triangle_to_weighted_floor hh hk hC, sum_vals hh,
      weighted_floor_from_residue hh hC.symm, sum_fraction_sq hh]
    field_simp [hH] <;> ring
  linear_combination -(hFirst.symm.trans hSecond)

theorem dedekindSum_reciprocity {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) :
    dedekindSum (h : ℤ) k + dedekindSum (k : ℤ) h =
      ((h : ℚ) ^ 2 + (k : ℚ) ^ 2 - 3 * (h : ℚ) * (k : ℚ) + 1) /
        (12 * (h : ℚ) * (k : ℚ)) := by
  have hH : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hK : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  apply (eq_div_iff (by positivity : 12 * (h : ℚ) * (k : ℚ) ≠ 0)).2
  rw [mul_comm]
  exact dedekindSum_reciprocity_scaled hh hk hC

end ManuscriptAudit.Paper8DedekindReciprocity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindReciprocity.dedekindSum_reciprocity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
