import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicHenselGate

/-!
# The actual discriminant gate for monic integral polynomials

The Sylvester determinant commutes with reduction at fixed degrees.
For a monic polynomial, reducing coefficients can lower the derivative
degree without changing the resultant. The library's discriminant
formula then turns nonvanishing of the integral discriminant into the
unique-lift criterion over the p-adic integers.
-/

namespace ManuscriptAudit.PadicDiscriminantGate

open Polynomial

noncomputable section

/-- Nonzero reduced discriminant implies nonzero resultant of the actual reduced polynomial. -/
theorem mapped_resultant_ne_zero_of_monic_discr {R S : Type*} [CommRing R] [Field S]
    (F : R[X]) (ρ : R →+* S) (hMonic : F.Monic) (hDeg : 0 < F.degree)
    (hDisc : ρ F.discr ≠ 0) :
    resultant (F.map ρ) (derivative (F.map ρ)) ≠ 0 := by
  let f := F.map ρ
  let g := F.derivative.map ρ
  have hf : f.Monic := hMonic.map ρ
  have hF : f.natDegree = F.natDegree := hMonic.natDegree_map ρ
  have hg : g.natDegree ≤ F.natDegree - 1 :=
    (Polynomial.natDegree_map_le).trans (Polynomial.natDegree_derivative_le F)
  have hPad : resultant f g F.natDegree (F.natDegree - 1) ≠ 0 := by
    have hSign : (-1 : S) ^ (F.natDegree * (F.natDegree - 1) / 2) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hLead : ρ F.leadingCoeff ≠ 0 := by
      rw [hMonic.leadingCoeff, map_one]
      exact one_ne_zero
    simpa only [f, g, Polynomial.resultant_map_map, Polynomial.resultant_deriv hDeg,
      map_mul, map_pow, map_neg, map_one] using
        mul_ne_zero (mul_ne_zero hSign hLead) hDisc
  have hSize := Polynomial.resultant_add_right_deg f g f.natDegree g.natDegree
    (F.natDegree - 1 - g.natDegree) (le_rfl : g.natDegree ≤ g.natDegree)
  rw [Nat.add_sub_cancel' hg, Polynomial.coeff_natDegree, hf, one_pow, one_mul] at hSize
  change resultant f (derivative (F.map ρ)) ≠ 0
  rw [Polynomial.derivative_map]
  change resultant f g ≠ 0
  intro hZero
  apply hPad
  calc
    resultant f g F.natDegree (F.natDegree - 1) =
        resultant f g f.natDegree (F.natDegree - 1) :=
      congrArg (fun m => resultant f g m (F.natDegree - 1)) hF.symm
    _ = resultant f g := hSize
    _ = 0 := hZero

/-- Exact good-locus Hensel criterion using the integral discriminant and actual coefficient maps. -/
theorem monic_integral_discr_unique_lift {p : ℕ} [Fact p.Prime]
    (F : ℤ[X]) (hMonic : F.Monic) (hDeg : 0 < F.degree)
    (hDisc : (F.discr : ZMod p) ≠ 0) (r : ZMod p) :
    (F.map (Int.castRingHom (ZMod p))).eval r = 0 ↔
      ∃! z : ℤ_[p], (F.map (Int.castRingHom (ℤ_[p]))).eval z = 0 ∧
        PadicInt.toZMod z = r := by
  let Fp := F.map (Int.castRingHom (ZMod p))
  let Fpadic := F.map (Int.castRingHom (ℤ_[p]))
  have hComp :
      (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp (Int.castRingHom (ℤ_[p])) =
        Int.castRingHom (ZMod p) := Subsingleton.elim _ _
  have hF : Fpadic.map PadicInt.toZMod = Fp := by
    change (F.map (Int.castRingHom (ℤ_[p]))).map PadicInt.toZMod =
      F.map (Int.castRingHom (ZMod p))
    rw [Polynomial.map_map, hComp]
  have hf : Fp ≠ 0 := (hMonic.map _).ne_zero
  have h : resultant Fp (derivative Fp) ≠ 0 :=
    mapped_resultant_ne_zero_of_monic_discr F _ hMonic hDeg hDisc
  have hf' : Fpadic.map PadicInt.toZMod ≠ 0 := by rw [hF]; exact hf
  have h' : resultant (Fpadic.map PadicInt.toZMod)
      (derivative (Fpadic.map PadicInt.toZMod)) ≠ 0 := by rw [hF]; exact h
  have e := PadicHenselGate.resultant_good_residue_lift Fpadic r hf' h'
  change Fp.eval r = 0 ↔ ∃! z : ℤ_[p], Fpadic.eval z = 0 ∧ PadicInt.toZMod z = r
  simpa only [hF] using e

end

end ManuscriptAudit.PadicDiscriminantGate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicDiscriminantGate.mapped_resultant_ne_zero_of_monic_discr,
      ``ManuscriptAudit.PadicDiscriminantGate.monic_integral_discr_unique_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
