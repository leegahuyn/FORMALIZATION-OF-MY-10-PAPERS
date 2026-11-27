import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicLangPowers
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitAllInertTate
import PrimalitySheafVerification.ManuscriptAudit.EisensteinRotationPowers

/-! All prime-to-p scalar operations are surjective on actual good split centered cubic points. -/

namespace ManuscriptAudit.CubicSplitScalarSurjectivity

open RotationNormUnit EisensteinRotationPowers EisensteinPowerCongruence
open CubicNonsplitThreeAdicTrace CubicCertifiedInertTate CubicSplitAllInertTate

noncomputable section

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]

/-- For every prime-to-p positive m, some actual Lang map factors through multiplication by m. -/
theorem scalar_surjective_of_reference (c : IntegralReference p L) {m : ℕ}
    (hm : m ≠ 0) (hc : p.Coprime m) :
    Function.Surjective (fun P : Points c => m • P) := by
  letI : NeZero m := ⟨hm⟩
  have hU : IsUnit ((c.a ^ 2 - c.a * c.b + c.b ^ 2 : ℤ) : ZMod m) := by
    rw [c.norm, Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hc
  obtain ⟨n, hn, ha, hb⟩ := exists_positive_power c.a c.b hU
  let v := coefficients c.a c.b n
  have hA : (m : ℤ) ∣ v.1 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_one, show (v.1 : ZMod m) = 1 from ha, sub_self]
  have hB : (m : ℤ) ∣ v.2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  let F := arithmeticPointFrobenius (ZMod p) L c.A
  have hPow : F ^ n - 1 = m • combination c.rotation x y := by
    calc
      _ = combination c.rotation (v.1 - 1) v.2 := by
        rw [show F = combination c.rotation c.a c.b from c.native,
          combination_pow c.rotation c.quadratic]
        simp only [combination, sub_zsmul, one_zsmul]
        abel
      _ = _ := by
        rw [hx, hy, ← natCast_zsmul (combination c.rotation x y)]
        simp only [combination, mul_zsmul, zsmul_add]
  intro P
  obtain ⟨Q, hQ⟩ := CubicLangPowers.pow_sub_one_surjective p L c.goodPrime c.nonzeroA hn P
  change (F ^ n - 1) Q = P at hQ
  rw [hPow] at hQ
  let evaluate : AddMonoid.End (Points c) →+ Points c :=
    { toFun := fun U => U Q
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact ⟨combination c.rotation x y Q,
    (map_nsmul evaluate m (combination c.rotation x y)).symm.trans hQ⟩

/-- Every good split prime-field cubic is divisible by every positive integer coprime to p. -/
theorem scalar_surjective {L : Type} [Field L] [Algebra (ZMod p) L]
    [DecidableEq L] [IsAlgClosed L] (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (hc : p.Coprime m) :
    Function.Surjective (fun P : GeometricPoints (ZMod p) L A => m • P) :=
  scalar_surjective_of_reference (reference p L hp hs hA) hm hc

end

end ManuscriptAudit.CubicSplitScalarSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitScalarSurjectivity.scalar_surjective_of_reference,
      ``ManuscriptAudit.CubicSplitScalarSurjectivity.scalar_surjective] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
