import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossDoubleCosets
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCentralSign

/-! The normalized odd cross rows and their right translates exhaust actual level-four left cusp orbits. -/

namespace ManuscriptAudit.Paper8OddCrossOrbitRows

open Matrix Paper8OddCrossCuspRows Paper8OddCrossCuspNormalization Paper8OddCrossDoubleCosets
open Paper8OddCrossPoincareConvergence Paper8OddCrossCuspActualMultiplier Paper8EtaCentralSign
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq)
open scoped MatrixGroups

noncomputable section

private theorem crossShift_crossShift (g : SL(2, ℤ)) (m n p q : ℤ) :
    crossShift (crossShift g m n) p q = crossShift g (p + m) (n + q) := by
  unfold crossShift
  rw [show 4 * (n + q) = 4 * n + 4 * q by ring, _root_.zpow_add ModularGroup.T p m, _root_.zpow_add ModularGroup.T (4 * n) (4 * q)]
  simp only [mul_assoc]

theorem every_positive_cross_matrix (g : SL(2, ℤ)) (hPos : 0 < g 1 0)
    (hLevel : g * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4) :
    ∃ (D : ℕ) (A : CrossRow (D + 1)) (m n : ℤ), g = crossShift A.matrix m n := by
  let c : ℕ := Int.toNat (g 1 0)
  have hC : g 1 0 = (c : ℤ) := (Int.toNat_of_nonneg hPos.le).symm
  have hc : 0 < c := by
    rw [hC] at hPos
    exact_mod_cast hPos
  let D := c - 1
  have hCD : D + 1 = c := Nat.sub_add_cancel hc
  have hM : g 1 0 = ((D + 1 : ℕ) : ℤ) := by rwa [hCD]
  let A := normalizeCrossRow (Nat.succ_pos D) g hM hLevel
  let m := g 0 0 / ((D + 1 : ℕ) : ℤ)
  let n := g 1 1 / (4 * ((D + 1 : ℕ) : ℤ))
  refine ⟨D, A, m, n, ?_⟩
  change g = crossShift (normalizeCrossRow (Nat.succ_pos D) g hM hLevel).matrix m n
  rw [normalizeCrossRow_matrix]
  change g = crossShift (crossShift g (-m) (-n)) m n
  rw [crossShift_crossShift, add_neg_cancel, neg_add_cancel]
  simp [crossShift]

private theorem crossGroupElement_shift_mul_S_inv {D : ℕ} (A : CrossRow D) (m n : ℤ) :
    crossShift A.matrix m n * ModularGroup.S⁻¹ =
      ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ)) := by
  unfold crossShift
  change ModularGroup.T ^ m * A.matrix * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹ =
    ModularGroup.T ^ m * (A.matrix * ModularGroup.S⁻¹) *
      (ModularGroup.S * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹)
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem cuspCross_lowerLeft (g : SL(2, ℤ)) :
    (g * ModularGroup.S) 1 0 = g 1 1 := by
  change (g.1 * ModularGroup.S.1) 1 0 = _
  rw [ModularGroup.coe_S]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cuspCross_nonzero (g : CongruenceSubgroup.Gamma0 4) :
    ((g : SL(2, ℤ)) * ModularGroup.S) 1 0 ≠ 0 := by
  rw [cuspCross_lowerLeft]
  intro hd
  have h := levelCharacter_sq g
  rw [levelCharacter_apply, hd, Int.cast_zero] at h
  have h0 : chiFour (0 : ZMod 4) = 0 := by decide
  rw [h0, Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  exact zero_ne_one h

private theorem positive_group_cross_rep (g : CongruenceSubgroup.Gamma0 4)
    (hPos : 0 < ((g : SL(2, ℤ)) * ModularGroup.S) 1 0) :
    ∃ (D : ℕ) (A : CrossRow (D + 1)) (m n : ℤ),
      (g : SL(2, ℤ)) =
        ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ)) := by
  have hBack : (g : SL(2, ℤ)) * ModularGroup.S * ModularGroup.S⁻¹ = g := by
    simp [mul_assoc]
  have hL : (g : SL(2, ℤ)) * ModularGroup.S * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4 :=
    hBack.symm ▸ g.property
  obtain ⟨D, A, m, n, h⟩ := every_positive_cross_matrix _ hPos hL
  refine ⟨D, A, m, n, ?_⟩
  calc
    _ = (g : SL(2, ℤ)) * ModularGroup.S * ModularGroup.S⁻¹ := hBack.symm
    _ = crossShift A.matrix m n * ModularGroup.S⁻¹ := congrArg (fun M => M * ModularGroup.S⁻¹) h
    _ = _ := crossGroupElement_shift_mul_S_inv A m n

private theorem central_multiply_lowerLeft (g : SL(2, ℤ)) :
    ((-1 : SL(2, ℤ)) * g) 1 0 = -(g 1 0) := by
  change ((-(1 : Matrix (Fin 2) (Fin 2) ℤ)) * g.1) 1 0 = _
  simp [Matrix.neg_apply]

private theorem central_square : (-1 : SL(2, ℤ)) * (-1 : SL(2, ℤ)) = 1 := by
  apply Subtype.ext
  change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) * (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) = 1
  simp

theorem actual_cross_rows_exhaust (g : CongruenceSubgroup.Gamma0 4) :
    ∃ (e : Bool) (D : ℕ) (A : CrossRow (D + 1)) (m n : ℤ),
      (g : SL(2, ℤ)) =
        (if e then -1 else 1) * ModularGroup.T ^ m *
          (crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ)) := by
  rcases lt_or_gt_of_ne (cuspCross_nonzero g) with h | h
  · let gp := centralNeg 4 * g
    have hP : 0 < ((gp : SL(2, ℤ)) * ModularGroup.S) 1 0 := by
      change 0 < ((-1 : SL(2, ℤ)) * (g : SL(2, ℤ)) * ModularGroup.S) 1 0
      rw [mul_assoc, central_multiply_lowerLeft]
      exact neg_pos.mpr h
    obtain ⟨D, A, m, n, hRep⟩ := positive_group_cross_rep gp hP
    refine ⟨true, D, A, m, n, ?_⟩
    have hRep' : (-1 : SL(2, ℤ)) * (g : SL(2, ℤ)) =
        ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ)) := hRep
    have hh := congrArg (fun M : SL(2, ℤ) => (-1 : SL(2, ℤ)) * M) hRep'
    simpa only [if_pos trivial, ← mul_assoc, central_square, one_mul] using hh
  · obtain ⟨D, A, m, n, hRep⟩ := positive_group_cross_rep g h
    exact ⟨false, D, A, m, n, by simpa using hRep⟩

theorem actual_cross_rows_left_translate_unique {D E : ℕ}
    (A : CrossRow (D + 1)) (B : CrossRow (E + 1)) (m n q : ℤ)
    (h : ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ)) =
      (crossGroupElement B : SL(2, ℤ)) * (rightCuspStabilizer q : SL(2, ℤ))) :
    m = 0 ∧ n = q ∧ ∃ hDE : D = E, (hDE ▸ A) = B := by
  have hS := congrArg (fun X : SL(2, ℤ) => X * ModularGroup.S) h
  have hA : ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) *
      (rightCuspStabilizer n : SL(2, ℤ)) * ModularGroup.S = crossShift A.matrix m n := by
    rw [← crossGroupElement_shift_mul_S_inv]
    simp [mul_assoc]
  have hB : (crossGroupElement B : SL(2, ℤ)) * (rightCuspStabilizer q : SL(2, ℤ)) *
      ModularGroup.S = crossShift B.matrix 0 q := by
    have h0 := congrArg (fun X : SL(2, ℤ) => X * ModularGroup.S)
      (crossGroupElement_shift_mul_S_inv B 0 q)
    simpa [mul_assoc] using h0.symm
  change ModularGroup.T ^ m * (crossGroupElement A : SL(2, ℤ)) *
      (rightCuspStabilizer n : SL(2, ℤ)) * ModularGroup.S =
    (crossGroupElement B : SL(2, ℤ)) * (rightCuspStabilizer q : SL(2, ℤ)) * ModularGroup.S at hS
  rw [hA, hB] at hS
  have hC := congrArg (fun X : SL(2, ℤ) => X 1 0) hS
  change (crossShift A.matrix m n) 1 0 = (crossShift B.matrix 0 q) 1 0 at hC
  rw [(crossShift_entries A.matrix m n).2.1, (crossShift_entries B.matrix 0 q).2.1,
    A.lowerLeft, B.lowerLeft] at hC
  have hDE : D = E := by exact Nat.add_right_cancel (by exact_mod_cast hC : D + 1 = E + 1)
  subst E
  have hSet := congrArg (fun X => crossShift X 0 (-q)) hS
  change crossShift (crossShift A.matrix m n) 0 (-q) =
    crossShift (crossShift B.matrix 0 q) 0 (-q) at hSet
  rw [crossShift_crossShift, crossShift_crossShift, zero_add, add_neg_cancel] at hSet
  have hNorm : crossShift A.matrix m (n + -q) = B.matrix := by
    simpa [crossShift] using hSet
  obtain ⟨hm, hn, hAB⟩ := normalizedCross_shift_unique (Nat.succ_pos D) A B m (n + -q) hNorm
  exact ⟨hm, by omega, rfl, hAB⟩

end
end ManuscriptAudit.Paper8OddCrossOrbitRows

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossOrbitRows.actual_cross_rows_exhaust
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
