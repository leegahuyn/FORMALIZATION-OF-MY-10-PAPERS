import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicHasseCoefficient
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount

/-!
# The reduced cubic has no p-torsion over any finite extension

For p≡2 modulo 3, the Hasse coefficient vanishes in every finite
characteristic-p coefficient field. Counting actual projective points
then gives a group order congruent to one modulo p. The proof obtains torsion vanishing directly from the finite group of points.
-/

namespace ManuscriptAudit.CubicFiniteTorsion

open FiniteFieldPointCount

private theorem small_nat_cast_ne_zero {F : Type*} [Field F] (p : ℕ) [CharP F p]
    (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : F) ≠ 0 :=
  (CharP.cast_eq_zero_iff F p n).not.mpr (fun h => (not_le_of_gt hlt) (Nat.le_of_dvd hn h))

theorem shortCubic_zero_discriminant_ne_zero {F : Type*} [Field F]
    (p : ℕ) [CharP F p] (hp : 5 ≤ p) {A : F} (hA : A ≠ 0) :
    (shortCubic (0 : F) A).Δ ≠ 0 := by
  have h₃ : (3 : F) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using small_nat_cast_ne_zero (F := F) p 3 (by omega) (by omega)
  have h₄ : (4 : F) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using small_nat_cast_ne_zero (F := F) p 4 (by omega) (by omega)
  have hΔ : (shortCubic (0 : F) A).Δ = -((3 : F) ^ 3 * (4 * A) ^ 2) := by
    simp [shortCubic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> ring <;> simp
  rw [hΔ]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 h₃) (pow_ne_zero 2 (mul_ne_zero h₄ hA)))

/-- The count of actual projective points is one in the coefficient field. -/
theorem paper5_projective_count_cast_eq_one {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : F} (hA : A ≠ 0) :
    (Nat.card (shortCubic (0 : F) A).toProjective.Point : F) = 1 := by
  classical
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    omega
  have h := shortCubic_zero_count_cast_eq_one_sub_coeff hchar
    Fintype.one_lt_card (shortCubic_zero_discriminant_ne_zero p hp hA)
  obtain ⟨r, _, hrank⟩ := FiniteField.card F p
  rw [hrank, CubicHasse.paper5_cubic_prime_power_coefficient_zero A hp hr r.2,
    sub_zero] at h
  exact h

/-- In every finite characteristic-p field, the projective point group
of the printed reduction has trivial p-torsion. -/
theorem paper5_no_p_torsion_over_finite_field {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : F} (hA : A ≠ 0) (P : (shortCubic (0 : F) A).toProjective.Point)
    (hP : p • P = 0) : P = 0 := by
  let n := Nat.card (shortCubic (0 : F) A).toProjective.Point
  have hn : (n : F) = 1 := paper5_projective_count_cast_eq_one hp hr hA
  have hnd : ¬ p ∣ n := by
    intro h
    exact zero_ne_one (((CharP.cast_eq_zero_iff F p n).mpr h).symm.trans hn)
  have hc : p.Coprime n := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnd
  have hd : addOrderOf P ∣ p.gcd n :=
    Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hP) (addOrderOf_dvd_natCard P)
  rw [hc.gcd_eq_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end ManuscriptAudit.CubicFiniteTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFiniteTorsion.shortCubic_zero_discriminant_ne_zero,
      ``ManuscriptAudit.CubicFiniteTorsion.paper5_projective_count_cast_eq_one,
      ``ManuscriptAudit.CubicFiniteTorsion.paper5_no_p_torsion_over_finite_field] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
