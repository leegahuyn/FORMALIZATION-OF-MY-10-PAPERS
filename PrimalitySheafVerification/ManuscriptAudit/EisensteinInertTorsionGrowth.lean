import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.EisensteinNormInert
import PrimalitySheafVerification.ManuscriptAudit.EisensteinPrimitiveFactor
import PrimalitySheafVerification.ManuscriptAudit.EisensteinRotationPowers
import PrimalitySheafVerification.ManuscriptAudit.RotationKernelPrimaryCardinality
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionCofinalCard

/-! The integer Frobenius identity and exact fixed counts give all inert-prime torsion cardinalities. -/

namespace ManuscriptAudit.EisensteinInertTorsionGrowth

open TorsionFrobeniusModule PowerTorsionTower PowerTorsionCofinalCard
open EisensteinPowerCongruence EisensteinPrimitiveFactor EisensteinRotationPowers
open EisensteinNormInert RotationNormUnit RotationKernelPrimaryCardinality Paper5PrintedRecurrence

noncomputable section

set_option maxHeartbeats 1400000

variable {G : Type*} [AddCommGroup G]

/-- The exact native endomorphism and arithmetic fixed-point count determine all torsion
levels and onto transitions at every inert prime coprime to its norm. -/
theorem card_and_transition (l q : ℕ) [Fact l.Prime] (hl : l % 3 = 2) (hq : 1 < q)
    (hc : q.Coprime l) (r F : AddMonoid.End G) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ)
    (hF : F = combination r a b) (hNorm : a ^ 2 - a * b + b ^ 2 = (q : ℤ))
    (hFixed : ∀ n : ℕ, 0 < n →
      Finite ↥((F ^ n - 1).ker) ∧
      (Nat.card ↥((F ^ n - 1).ker) : ℤ) =
        ((q ^ n : ℕ) : ℤ) + 1 - recurrence q (2 * a - b) n) :
    (∀ n, Nat.card (PowerTorsion l G n) = (l ^ 2) ^ n) ∧
      ∀ n, Function.Surjective (transition l G n) := by
  have lPrime : l.Prime := Fact.out
  apply card_and_surjective_of_cofinal_exact l G (pow_pos lPrime.pos 2)
  intro N
  letI : NeZero (l ^ N) := ⟨pow_ne_zero _ lPrime.ne_zero⟩
  have hUnit : IsUnit ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod (l ^ N)) := by
    rw [hNorm, Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right N)
  obtain ⟨k, hk, hA, hB⟩ := exists_positive_power a b hUnit
  let v := coefficients a b k
  have hA' : (↑(l ^ N) : ℤ) ∣ v.1 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_one, show (v.1 : ZMod (l ^ N)) = 1 from hA, sub_self]
  have hB' : (↑(l ^ N) : ℤ) ∣ v.2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hB
  have hNZ : v.1 - 1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra! h
    have hqk : (1 : ℤ) < (q : ℤ) ^ k := by
      exact_mod_cast (by simpa only [one_pow] using Nat.pow_lt_pow_left hq hk.ne' :
        1 < q ^ k)
    have hn : v.1 ^ 2 - v.1 * v.2 + v.2 ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ k :=
      norm_coefficients a b k
    rw [sub_eq_zero.mp h.1, h.2, hNorm] at hn
    exact (ne_of_lt hqk) (by simpa using hn)
  obtain ⟨t, u, w, ht, hu, hw, hPrim⟩ := exists_primitive_factor l (v.1 - 1) v.2 N hA' hB' hNZ
  let d := (u ^ 2 - u * w + w ^ 2).toNat
  have hD : (d : ℤ) = u ^ 2 - u * w + w ^ 2 := Int.toNat_of_nonneg (by
    nlinarith [sq_nonneg (2 * u - w), sq_nonneg w])
  have hd : ¬l ∣ d := by
    intro hv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) l).mpr (Int.natCast_dvd_natCast.mpr hv)
    have hN := norm_ne_zero l hl hPrim
    apply hN
    rwa [hD, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow] at hz
  have hPow : F ^ k - 1 = (l ^ t : ℕ) • combination r u w := by
    calc
      _ = combination r (v.1 - 1) v.2 := by
        rw [hF, combination_pow r hr]
        simp only [combination, sub_zsmul, one_zsmul]
        abel
      _ = _ := by
        rw [hu, hw, ← natCast_zsmul (combination r u w)]
        simp only [combination, mul_zsmul, zsmul_add]
  obtain ⟨hFin, hK⟩ := hFixed k hk
  have hArit :
      (Nat.card ↥((F ^ k - 1).ker) : ℤ) = ((l ^ t) ^ 2 * d : ℕ) := by
    rw [hK, ← difference_norm_eq_count a b q hNorm k]
    change (v.1 - 1) ^ 2 - (v.1 - 1) * v.2 + v.2 ^ 2 = _
    rw [hu, hw, Nat.cast_mul, Nat.cast_pow, hD]
    ring
  have hCount : Nat.card ↥((F ^ k - 1).ker) = (l ^ t) ^ 2 * d := by exact_mod_cast hArit
  rw [hPow] at hFin hCount
  exact ⟨t, ht, card_torsion_of_kernel l t d r hr u w hD hd hFin hCount⟩

end
end ManuscriptAudit.EisensteinInertTorsionGrowth

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EisensteinInertTorsionGrowth.card_and_transition
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
