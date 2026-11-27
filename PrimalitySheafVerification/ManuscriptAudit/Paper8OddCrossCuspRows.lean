import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8NormalizedKloostermanRows

/-!
# Odd modulus classes as a cross-cusp character on Γ₀(4)

For odd D, right translation by a unique residue modulo four sends a
normalized row A to a cross-cusp row with A T^m S⁻¹ in Γ₀(4).
Its lower right entry is D, so the Dirichlet character on the subgroup
detects exactly the two odd classes of D.
-/

namespace ManuscriptAudit.Paper8OddCrossCuspRows

open Matrix Paper8NormalizedKloostermanRows
open scoped MatrixGroups

def chiFour (x : ZMod 4) : ℤ :=
  if x = 1 then 1 else if x = 3 then -1 else 0

private theorem chiFour_mul : ∀ x y : ZMod 4, chiFour (x * y) = chiFour x * chiFour y := by
  decide

def levelCharacter : CongruenceSubgroup.Gamma0 4 →* ℤ where
  toFun g := chiFour (CongruenceSubgroup.Gamma0Map 4 g)
  map_one' := by rw [map_one] <;> decide
  map_mul' g h := by rw [map_mul, chiFour_mul]

theorem levelCharacter_apply (g : CongruenceSubgroup.Gamma0 4) :
    levelCharacter g = chiFour (g.1 1 1 : ZMod 4) :=
  rfl

def cuspTranslate (A : SL(2, ℤ)) (m : ℤ) : SL(2, ℤ) :=
  A * ModularGroup.T ^ m * ModularGroup.S⁻¹

theorem cuspTranslate_entries (A : SL(2, ℤ)) (m : ℤ) :
    cuspTranslate A m 1 0 = -(A 1 1 + A 1 0 * m) ∧
    cuspTranslate A m 1 1 = A 1 0 := by
  have hS : (ModularGroup.S⁻¹).1 = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
    change (↑(ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [ModularGroup.S_inv, SpecialLinearGroup.coe_neg, ModularGroup.coe_S]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  constructor
  · change ((A.1 * (ModularGroup.T ^ m).1) * (ModularGroup.S⁻¹).1) 1 0 = _
    rw [hS, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · change ((A.1 * (ModularGroup.T ^ m).1) * (ModularGroup.S⁻¹).1) 1 1 = _
    rw [hS, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem cuspTranslate_mem_iff {D : ℕ} (A : NormalizedRow D) (m : ZMod 4) :
    cuspTranslate A.1 (m.val : ℤ) ∈ CongruenceSubgroup.Gamma0 4 ↔
      (A.1 1 1 : ZMod 4) + (D : ZMod 4) * m = 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, (cuspTranslate_entries A.1 _).1, A.property.1]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val, neg_eq_zero]

private theorem odd_mod_four (D : ℕ) (hD : Odd D) : D % 4 = 1 ∨ D % 4 = 3 := by
  obtain ⟨k, hk⟩ := hD
  omega

private theorem odd_square_mod_four (D : ℕ) (hD : Odd D) : (D : ZMod 4) * D = 1 := by
  obtain h | h := odd_mod_four D hD
  · have hCast : (D : ZMod 4) = (1 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff' D 1 4).mpr (by simpa using h)
    rw [hCast] <;> decide
  · have hCast : (D : ZMod 4) = (3 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff' D 3 4).mpr (by simpa using h)
    rw [hCast] <;> decide

theorem unique_cuspTranslate {D : ℕ} (hD : Odd D) (A : NormalizedRow D) :
    ∃! m : ZMod 4, cuspTranslate A.1 (m.val : ℤ) ∈ CongruenceSubgroup.Gamma0 4 := by
  let d := (A.1 1 1 : ZMod 4)
  have hInv := odd_square_mod_four D hD
  refine ⟨-((D : ZMod 4) * d), (cuspTranslate_mem_iff A _).2 ?_, fun m hm => ?_⟩
  · change d + (D : ZMod 4) * -((D : ZMod 4) * d) = 0
    rw [mul_neg, ← mul_assoc, hInv, one_mul, add_neg_cancel]
  · have hEq := (cuspTranslate_mem_iff A m).1 hm
    change d + (D : ZMod 4) * m = 0 at hEq
    have hNeg : (D : ZMod 4) * m = -d := by
      simpa only [← add_assoc, neg_add_cancel, zero_add, add_zero] using
        congrArg (fun z : ZMod 4 => -d + z) hEq
    calc
      m = (D : ZMod 4) * ((D : ZMod 4) * m) := by rw [← mul_assoc, hInv, one_mul]
      _ = -((D : ZMod 4) * d) := by rw [hNeg, mul_neg]

theorem cuspTranslate_levelCharacter {D : ℕ} (A : NormalizedRow D) (m : ℤ)
    (h : cuspTranslate A.1 m ∈ CongruenceSubgroup.Gamma0 4) :
    levelCharacter ⟨cuspTranslate A.1 m, h⟩ =
      if D % 4 = 1 then 1 else if D % 4 = 3 then -1 else 0 := by
  rw [levelCharacter_apply]
  change chiFour ((cuspTranslate A.1 m 1 1 : ℤ) : ZMod 4) = _
  rw [(cuspTranslate_entries A.1 m).2, A.property.1, Int.cast_natCast, chiFour]
  have h1 : ((D : ZMod 4) = 1) ↔ D % 4 = 1 := by
    simpa using ZMod.natCast_eq_natCast_iff' D 1 4
  have h3 : ((D : ZMod 4) = 3) ↔ D % 4 = 3 := by
    simpa using ZMod.natCast_eq_natCast_iff' D 3 4
  simp only [h1, h3]

end ManuscriptAudit.Paper8OddCrossCuspRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossCuspRows.levelCharacter_apply,
      ``ManuscriptAudit.Paper8OddCrossCuspRows.cuspTranslate_entries,
      ``ManuscriptAudit.Paper8OddCrossCuspRows.cuspTranslate_mem_iff,
      ``ManuscriptAudit.Paper8OddCrossCuspRows.unique_cuspTranslate,
      ``ManuscriptAudit.Paper8OddCrossCuspRows.cuspTranslate_levelCharacter] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
