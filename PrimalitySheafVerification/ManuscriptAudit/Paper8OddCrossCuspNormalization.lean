import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspRows

/-!
# Actual finite normalization at the pair of cusps infinity and zero

Before the positive diagonal rescaling, the fixed-modulus representatives
have (0≤a<D), (0≤d<4D) and satisfy A S⁻¹∈Γ₀(4).
For odd positive D they are equivalent to the full-level normalized rows.
-/

namespace ManuscriptAudit.Paper8OddCrossCuspNormalization

open Matrix Paper8NormalizedKloostermanRows Paper8OddCrossCuspRows
open scoped MatrixGroups

@[ext]
structure CrossRow (D : ℕ) where
  matrix : SL(2, ℤ)
  lowerLeft : matrix 1 0 = (D : ℤ)
  topNonneg : 0 ≤ matrix 0 0
  topBound : matrix 0 0 < (D : ℤ)
  bottomNonneg : 0 ≤ matrix 1 1
  bottomBound : matrix 1 1 < 4 * (D : ℤ)
  atLevel : matrix * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4

theorem crossRow_odd {D : ℕ} (A : CrossRow D) : Odd D := by
  let g := A.matrix * ModularGroup.S⁻¹
  have hBottom : g 1 1 = (D : ℤ) := by
    have h := (cuspTranslate_entries A.matrix 0).2
    simpa only [cuspTranslate, zpow_zero, mul_one, A.lowerLeft, g] using h
  have hLow4 : (g 1 0 : ZMod 4) = 0 := (CongruenceSubgroup.Gamma0_mem).1 A.atLevel
  have hDvd4 : (4 : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 hLow4
  have hLow2 : (g 1 0 : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2
      ((by decide : (2 : ℤ) ∣ 4).trans hDvd4)
  have hDet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  have hUnit : (g 0 0 : ZMod 2) * (D : ZMod 2) = 1 := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one, hBottom, Int.cast_natCast,
      hLow2, mul_zero, sub_zero] using congrArg (fun w : ℤ => (w : ZMod 2)) hDet
  by_contra hOdd
  have hMod : D % 2 = 0 := by
    have hh : D % 2 ≠ 1 := fun hm => hOdd (Nat.odd_iff.mpr hm)
    omega
  rw [(ZMod.natCast_eq_zero_iff D 2).2 (Nat.dvd_iff_mod_eq_zero.2 hMod), mul_zero] at hUnit
  exact zero_ne_one hUnit

theorem rightTranslation_entries (A : SL(2, ℤ)) (m : ℤ) :
    (A * ModularGroup.T ^ m) 0 0 = A 0 0 ∧
    (A * ModularGroup.T ^ m) 1 0 = A 1 0 ∧
    (A * ModularGroup.T ^ m) 1 1 = A 1 1 + A 1 0 * m := by
  constructor
  · change (A.1 * (ModularGroup.T ^ m).1) 0 0 = _
    rw [ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · change (A.1 * (ModularGroup.T ^ m).1) 1 0 = _
    rw [ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · change (A.1 * (ModularGroup.T ^ m).1) 1 1 = _
    rw [ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

noncomputable section

def chosenShift {D : ℕ} (hOdd : Odd D) (A : NormalizedRow D) : ZMod 4 :=
  Classical.choose (unique_cuspTranslate hOdd A).exists

theorem chosenShift_mem {D : ℕ} (hOdd : Odd D) (A : NormalizedRow D) :
    cuspTranslate A.1 ((chosenShift hOdd A).val : ℤ) ∈ CongruenceSubgroup.Gamma0 4 :=
  Classical.choose_spec (unique_cuspTranslate hOdd A).exists

theorem chosenShift_unique {D : ℕ} (hOdd : Odd D) (A : NormalizedRow D) (m : ZMod 4)
    (hm : cuspTranslate A.1 (m.val : ℤ) ∈ CongruenceSubgroup.Gamma0 4) :
    m = chosenShift hOdd A := by
  obtain ⟨r, _, hr⟩ := unique_cuspTranslate hOdd A
  exact (hr m hm).trans (hr _ (chosenShift_mem hOdd A)).symm

def toCross {D : ℕ} (hD : 0 < D) (hOdd : Odd D) (A : NormalizedRow D) : CrossRow D := by
  let m : ℤ := (chosenShift hOdd A).val
  let g := A.1 * ModularGroup.T ^ m
  have hEntries := rightTranslation_entries A.1 m
  have ha := hEntries.1
  have hc := hEntries.2.1
  have hd := hEntries.2.2
  have hDInt : 0 < (D : ℤ) := by exact_mod_cast hD
  have hm0 : 0 ≤ m := Int.natCast_nonneg _
  have hm4 : m < 4 := Int.ofNat_lt.mpr (ZMod.val_lt (chosenShift hOdd A))
  have hm3 : m ≤ 3 := by omega
  have hlow : 0 ≤ A.1 1 1 + (D : ℤ) * m :=
    add_nonneg A.property.2.2.1 (mul_nonneg hDInt.le hm0)
  have hu := mul_le_mul_of_nonneg_left hm3 hDInt.le
  have hhigh : A.1 1 1 + (D : ℤ) * m < 4 * (D : ℤ) := by
    linarith [A.property.2.2.2]
  refine ⟨g, hc.trans A.property.1, ?_, ?_, ?_, ?_, chosenShift_mem hOdd A⟩
  · change 0 ≤ (A.1 * ModularGroup.T ^ m) 0 0
    rw [ha]
    exact A.property.2.1.1
  · change (A.1 * ModularGroup.T ^ m) 0 0 < (D : ℤ)
    rw [ha]
    exact A.property.2.1.2
  · change 0 ≤ (A.1 * ModularGroup.T ^ m) 1 1
    rw [hd, A.property.1]
    exact hlow
  · change (A.1 * ModularGroup.T ^ m) 1 1 < 4 * (D : ℤ)
    rw [hd, A.property.1]
    exact hhigh

def fromCross {D : ℕ} (hD : 0 < D) (A : CrossRow D) : NormalizedRow D := by
  let m : ℤ := A.matrix 1 1 / (D : ℤ)
  let g := A.matrix * ModularGroup.T ^ (-m)
  have hEntries := rightTranslation_entries A.matrix (-m)
  have ha := hEntries.1
  have hc := hEntries.2.1
  have hd := hEntries.2.2
  have hDInt : 0 < (D : ℤ) := by exact_mod_cast hD
  have hdmod : g 1 1 = A.matrix 1 1 % (D : ℤ) := by
    change (A.matrix * ModularGroup.T ^ (-m)) 1 1 = _
    rw [hd, A.lowerLeft]
    have hDiv := Int.emod_add_mul_ediv (A.matrix 1 1) (D : ℤ)
    dsimp only [m]
    linarith
  refine ⟨g, hc.trans A.lowerLeft, ?_, ?_⟩
  · change 0 ≤ (A.matrix * ModularGroup.T ^ (-m)) 0 0 ∧
      (A.matrix * ModularGroup.T ^ (-m)) 0 0 < (D : ℤ)
    rw [ha]
    exact ⟨A.topNonneg, A.topBound⟩
  · rw [hdmod]
    exact ⟨Int.emod_nonneg _ hDInt.ne', Int.emod_lt_of_pos _ hDInt⟩

theorem toCross_matrix {D : ℕ} (hD : 0 < D) (hOdd : Odd D) (A : NormalizedRow D) :
    (toCross hD hOdd A).matrix = A.1 * ModularGroup.T ^ ((chosenShift hOdd A).val : ℤ) :=
  rfl

theorem fromCross_matrix {D : ℕ} (hD : 0 < D) (A : CrossRow D) :
    (fromCross hD A).1 = A.matrix * ModularGroup.T ^ (-(A.matrix 1 1 / (D : ℤ))) :=
  rfl

theorem fromCross_toCross {D : ℕ} (hD : 0 < D) (hOdd : Odd D) (A : NormalizedRow D) :
    fromCross hD (toCross hD hOdd A) = A := by
  let m : ℤ := (chosenShift hOdd A).val
  have hDInt : 0 < (D : ℤ) := by exact_mod_cast hD
  have hShift : ((A.1 * ModularGroup.T ^ m) 1 1) / (D : ℤ) = m := by
    rw [(rightTranslation_entries A.1 m).2.2, A.property.1,
      Int.add_mul_ediv_left _ _ hDInt.ne',
      Int.ediv_eq_zero_of_lt A.property.2.2.1 A.property.2.2.2, zero_add]
  apply Subtype.ext
  rw [fromCross_matrix, toCross_matrix]
  change (A.1 * ModularGroup.T ^ m) *
    ModularGroup.T ^ (-(((A.1 * ModularGroup.T ^ m) 1 1) / (D : ℤ))) = A.1
  rw [hShift, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

theorem toCross_fromCross {D : ℕ} (hD : 0 < D) (hOdd : Odd D) (A : CrossRow D) :
    toCross hD hOdd (fromCross hD A) = A := by
  let q : ℤ := A.matrix 1 1 / (D : ℤ)
  have hDInt : 0 < (D : ℤ) := by exact_mod_cast hD
  have hq0 : 0 ≤ q := Int.ediv_nonneg A.bottomNonneg hDInt.le
  have hq4 : q < 4 := (Int.ediv_lt_iff_lt_mul hDInt).2 A.bottomBound
  let z : ZMod 4 := (q.toNat : ℕ)
  have hz : (z.val : ℤ) = q := by
    have hqN : q.toNat < 4 := by omega
    change (((q.toNat : ZMod 4).val : ℕ) : ℤ) = q
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqN, Int.toNat_of_nonneg hq0]
  have hLevel : cuspTranslate (fromCross hD A).1 (z.val : ℤ) ∈
      CongruenceSubgroup.Gamma0 4 := by
    rw [cuspTranslate, fromCross_matrix]
    change (A.matrix * ModularGroup.T ^ (-q)) * ModularGroup.T ^ (z.val : ℤ) *
      ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4
    rw [hz, mul_assoc A.matrix, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    exact A.atLevel
  have hChoice := chosenShift_unique hOdd (fromCross hD A) z hLevel
  have hMat : (toCross hD hOdd (fromCross hD A)).matrix = A.matrix := by
    rw [toCross_matrix, fromCross_matrix]
    change (A.matrix * ModularGroup.T ^ (-q)) *
      ModularGroup.T ^ ((chosenShift hOdd (fromCross hD A)).val : ℤ) = A.matrix
    rw [← hChoice, hz, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  exact CrossRow.ext hMat

def crossRowsEquiv {D : ℕ} (hD : 0 < D) (hOdd : Odd D) :
    NormalizedRow D ≃ CrossRow D where
  toFun := toCross hD hOdd
  invFun := fromCross hD
  left_inv := fromCross_toCross hD hOdd
  right_inv := toCross_fromCross hD hOdd

end
end ManuscriptAudit.Paper8OddCrossCuspNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossCuspNormalization.crossRow_odd,
      ``ManuscriptAudit.Paper8OddCrossCuspNormalization.rightTranslation_entries,
      ``ManuscriptAudit.Paper8OddCrossCuspNormalization.fromCross_toCross,
      ``ManuscriptAudit.Paper8OddCrossCuspNormalization.toCross_fromCross,
      ``ManuscriptAudit.Paper8OddCrossCuspNormalization.crossRowsEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
