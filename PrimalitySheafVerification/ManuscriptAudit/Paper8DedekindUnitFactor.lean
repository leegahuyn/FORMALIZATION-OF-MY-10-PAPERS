import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossJacobiSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8UnitReductionThree

/-! Exact summation of the two finite CRT factors of the manuscript's Dedekind coefficients. -/

namespace ManuscriptAudit.Paper8DedekindUnitFactor

open Finset Paper8ContourResidueWeights Paper8DedekindZeroReference Paper8OddCrossCuspPhase
open Paper8OddCrossJacobiSum Paper8UnitReductionThree Paper8ProductStationaryPhase Paper8ZModAdditiveCRT

noncomputable section

def referenceDedekindEntry (k : ℕ) (x : ZMod k) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (x.val : ℤ) k : ℝ) : ℂ))

theorem referenceZeroSum_native_units {k : ℕ} [NeZero k] :
    referenceZeroSum k = ∑ x : (ZMod k)ˣ, referenceDedekindEntry k x := by
  unfold referenceZeroSum
  rw [Finset.sum_subtype (p := fun d : Fin k => d.val.Coprime k) _ (by simp)]
  apply Fintype.sum_equiv (reducedFinToUnit k) _ _
  intro d
  unfold referenceDedekindEntry
  rw [reducedFinToUnit_val]

theorem referenceDedekindEntry_of_cast {h k : ℕ} [NeZero k] {z : ZMod k} (hz : (h : ZMod k) = z) :
    referenceDedekindEntry k z =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) := by
  have hE : ((z.val : ℤ) : ZMod k) = ((h : ℤ) : ZMod k) := by
    rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, hz]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ k).1 hE
  have hH : (h : ℤ) = (z.val : ℤ) + (k : ℤ) * q := by omega
  unfold referenceDedekindEntry
  rw [hH, dedekind_translate (Nat.pos_of_ne_zero (NeZero.ne k))]

private theorem sum_units_reduced_modulus {k q M : ℕ} [NeZero k] [NeZero q] [NeZero M]
    (hM : M = q * k) (hd : k ∣ M)
    (hBoth : ∀ a : ℕ, a.Coprime k → a.Coprime q) (F : ZMod k → ℂ) :
    (∑ x : (ZMod M)ˣ, F (ZMod.castHom hd (ZMod k) (x : ZMod M))) =
      (q : ℂ) * ∑ x : (ZMod k)ˣ, F x := by
  subst M
  have hF : ZMod.castHom hd (ZMod k) = (@reduceLowDigit q k) := RingHom.ext_zmod _ _
  rw [hF, sum_units_mul_lifts hBoth F]

theorem referenceZeroSum_factor_coprime {k q R S : ℕ} [NeZero k] [NeZero q] [NeZero R] [NeZero S]
    (hM : R * S = q * k) (hd : k ∣ R * S) (hC : R.Coprime S)
    (hBoth : ∀ a : ℕ, a.Coprime k → a.Coprime q) (E : ℂ)
    (F : (ZMod R)ˣ → ℂ) (G : (ZMod S)ˣ → ℂ)
    (hTerm : ∀ x : (ZMod (R * S))ˣ,
      referenceDedekindEntry k (ZMod.castHom hd (ZMod k) (x : ZMod (R * S))) =
        E * (F (unitsChineseRemainder hC x).1 * G (unitsChineseRemainder hC x).2)) :
    referenceZeroSum k = (q : ℂ)⁻¹ * E *
      (∑ x : (ZMod R)ˣ, F x) * (∑ x : (ZMod S)ˣ, G x) := by
  let H (x : (ZMod (R * S))ˣ) := referenceDedekindEntry k (ZMod.castHom hd (ZMod k) (x : ZMod (R * S)))
  have hMain : (∑ x : (ZMod (R * S))ˣ, H x) = (q : ℂ) * referenceZeroSum k := by
    unfold H
    rw [sum_units_reduced_modulus hM hd hBoth, ← referenceZeroSum_native_units]
  have hProduct : (∑ x : (ZMod (R * S))ˣ, H x) =
      E * ((∑ x : (ZMod R)ˣ, F x) * (∑ x : (ZMod S)ˣ, G x)) := by
    calc
      _ = ∑ xy : (ZMod R)ˣ × (ZMod S)ˣ, E * (F xy.1 * G xy.2) :=
        Fintype.sum_equiv (unitsChineseRemainder hC).toEquiv H (fun xy => E * (F xy.1 * G xy.2)) hTerm
      _ = _ := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
  have hEq := hMain.symm.trans hProduct
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  calc
    _ = (q : ℂ)⁻¹ * ((q : ℂ) * referenceZeroSum k) := by rw [← mul_assoc, inv_mul_cancel₀ hQ, one_mul]
    _ = _ := by rw [hEq]; ring

end
end ManuscriptAudit.Paper8DedekindUnitFactor

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindUnitFactor.referenceZeroSum_factor_coprime
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
