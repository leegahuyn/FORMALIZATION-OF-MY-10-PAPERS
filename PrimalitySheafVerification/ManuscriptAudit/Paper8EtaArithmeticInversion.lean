import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.RingTheory.Int.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindReciprocity
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindZeroReference
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaDedekindInversion
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspPhase

/-! The exact arithmetic Dedekind phase satisfies the same principal right-inversion rule as eta. -/

namespace ManuscriptAudit.Paper8EtaArithmeticInversion

open Matrix
open Paper8DedekindReciprocity Paper8DedekindZeroReference Paper8EtaDedekindInversion
open Paper8OddCrossCuspPhase
open Paper8ContourResidueWeights (dedekindSum)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

private theorem topLeft_mul_S (g : SL(2, ℤ)) : (g * ModularGroup.S) 0 0 = g 0 1 := by
  change (g.1 * ModularGroup.S.1) 0 0 = g 0 1
  rw [ModularGroup.coe_S]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem determinant_equation (g : SL(2, ℤ)) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  change Matrix.det g.1 = (1 : ℤ) at h
  rwa [Matrix.det_fin_two] at h

theorem explicitEta_mul_S (g : SL(2, ℤ)) {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hgc : g 1 0 = (c : ℤ)) (hgd : g 1 1 = (d : ℤ)) :
    explicitEta d ((g * ModularGroup.S) 0 0) ((g * ModularGroup.S) 1 1) =
      explicitEta c (g 0 0) (g 1 1) / Complex.sqrt Complex.I := by
  let a : ℤ := g 0 0
  let b : ℤ := g 0 1
  have hDet := determinant_equation g
  rw [hgc, hgd] at hDet
  change a * (d : ℤ) - b * (c : ℤ) = 1 at hDet
  have hCopZ : IsCoprime (d : ℤ) (c : ℤ) := by
    refine ⟨a, -b, ?_⟩
    rw [neg_mul, ← sub_eq_add_neg, hDet]
  have hCop : d.Coprime c := by
    simpa using Int.isCoprime_iff_nat_coprime.1 hCopZ
  have hC : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hD : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hDetR : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) = 1 := by
    exact_mod_cast hDet
  have hRec : (dedekindSum (d : ℤ) c : ℝ) + (dedekindSum (c : ℤ) d : ℝ) =
      ((d : ℝ) ^ 2 + (c : ℝ) ^ 2 - 3 * (d : ℝ) * (c : ℝ) + 1) /
        (12 * (d : ℝ) * (c : ℝ)) := by
    exact_mod_cast dedekindSum_reciprocity hd hc hCop
  have hDiff : integralDiagonal d b (-(c : ℤ)) - integralDiagonal c a (d : ℤ) =
      -(((c : ℝ) ^ 2 + (d : ℝ) ^ 2 + 1) / (24 * (c : ℝ) * (d : ℝ))) := by
    rw [← neg_div]
    have hP : (24 * (c : ℝ) * (d : ℝ)) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hC) hD
    apply (eq_div_iff hP).2
    calc
      _ = ((b : ℝ) - (c : ℝ)) * (c : ℝ) - ((a : ℝ) + (d : ℝ)) * (d : ℝ) := by
        unfold integralDiagonal
        push_cast
        field_simp [hC, hD] <;> ring
      _ = _ := by linear_combination -hDetR
  have hRhs :
      -(((c : ℝ) ^ 2 + (d : ℝ) ^ 2 + 1) / (24 * (c : ℝ) * (d : ℝ))) +
        (((d : ℝ) ^ 2 + (c : ℝ) ^ 2 - 3 * (d : ℝ) * (c : ℝ) + 1) /
          (12 * (d : ℝ) * (c : ℝ))) / 2 = -1 / 8 := by
    field_simp [hC, hD] <;> ring
  have hPhase :
      integralDiagonal d b (-(c : ℤ)) - ((dedekindSum (-(c : ℤ)) d : ℚ) : ℝ) / 2 - 1 / 8 =
        (integralDiagonal c a (d : ℤ) - (dedekindSum (d : ℤ) c : ℝ) / 2 - 1 / 8) - 1 / 8 := by
    rw [dedekindSum_neg, Rat.cast_neg]
    linarith [hDiff, hRec, hRhs]
  rw [topLeft_mul_S, (right_S_entries g).2, hgc, hgd]
  change explicitEta d b (-(c : ℤ)) = explicitEta c a (d : ℤ) / Complex.sqrt Complex.I
  unfold explicitEta
  rw [hPhase, sqrt_eq_exp Complex.I_ne_zero, Complex.log_I]
  apply (eq_div_iff (Complex.exp_ne_zero _)).2
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  unfold periodCoefficient
  push_cast
  ring

end ManuscriptAudit.Paper8EtaArithmeticInversion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaArithmeticInversion.explicitEta_mul_S
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
