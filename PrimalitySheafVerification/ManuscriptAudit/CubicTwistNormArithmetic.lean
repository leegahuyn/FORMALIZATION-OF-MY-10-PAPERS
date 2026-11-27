import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.PrimeToCharacteristicTorsion

/-! Arithmetic norms and fixed kernels for scalar multiplication. -/

namespace ManuscriptAudit.CubicTwistNormArithmetic

open TorsionFrobeniusModule

variable {G : Type*} [AddCommGroup G]

theorem scalar_kernel_eq (s : ℤ) :
    ((1 - s • (1 : AddMonoid.End G)).ker) = subgroup (1 - s).natAbs G := by
  ext x
  change x - s • x = 0 ↔ (1 - s).natAbs • x = 0
  have h : x - s • x = (1 - s) • x := by rw [sub_zsmul, one_zsmul]
  rw [h]
  generalize 1 - s = z
  cases z with
  | ofNat n => simp only [Int.natAbs_ofNat, natCast_zsmul]
  | negSucc n =>
    change (-((n + 1 : ℕ) : ℤ)) • x = 0 ↔ (n + 1) • x = 0
    rw [neg_zsmul, neg_eq_zero, natCast_zsmul]

theorem scalar_kernel_card (s : ℤ)
    (hCard : Nat.card (Torsion (1 - s).natAbs G) = (1 - s).natAbs ^ 2) :
    (Nat.card ↥((1 - s • (1 : AddMonoid.End G)).ker) : ℤ) = (1 - s) ^ 2 := by
  rw [scalar_kernel_eq]
  change (Nat.card (Torsion (1 - s).natAbs G) : ℤ) = _
  rw [hCard, Nat.cast_pow]
  generalize 1 - s = z
  cases z with
  | ofNat n => rfl
  | negSucc n =>
    change ((n + 1 : ℕ) : ℤ) ^ 2 = (-((n + 1 : ℕ) : ℤ)) ^ 2
    rw [neg_sq]

theorem scalar_norm_coprime (p : ℕ) (hp : p.Prime) {s : ℤ} (hs : (p : ℤ) ∣ s) :
    ¬ p ∣ (1 - s).natAbs := by
  intro h
  have hD : (p : ℤ) ∣ 1 - s := Int.natCast_dvd.mpr h
  have hOne : (p : ℤ) ∣ 1 := by
    have he := dvd_add hD hs
    rwa [sub_add_cancel] at he
  exact hp.not_dvd_one (by exact_mod_cast hOne)

theorem rotational_norm_pos (s : ℤ) : 0 < 1 + s + s * s := by
  nlinarith [sq_nonneg (2 * s + 1)]

theorem rotational_norm_coprime (p : ℕ) (hp : p.Prime) {s : ℤ} (hs : (p : ℤ) ∣ s) :
    ¬ p ∣ (1 + s + s * s).toNat := by
  intro h
  have he := Int.toNat_of_nonneg (le_of_lt (rotational_norm_pos s))
  have hD : (p : ℤ) ∣ 1 + s + s * s := by
    rw [← he]
    exact_mod_cast h
  have hTail : (p : ℤ) ∣ s + s * s := dvd_add hs (dvd_mul_of_dvd_left hs s)
  have hOne : (p : ℤ) ∣ 1 := by
    have hSub := dvd_sub hD hTail
    convert hSub using 1 <;> ring
  exact hp.not_dvd_one (by exact_mod_cast hOne)

end ManuscriptAudit.CubicTwistNormArithmetic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwistNormArithmetic.scalar_kernel_card,
      ``ManuscriptAudit.CubicTwistNormArithmetic.scalar_norm_coprime,
      ``ManuscriptAudit.CubicTwistNormArithmetic.rotational_norm_pos,
      ``ManuscriptAudit.CubicTwistNormArithmetic.rotational_norm_coprime] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
