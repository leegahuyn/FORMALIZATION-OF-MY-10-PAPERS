import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnits

/-! Laurent units have independent scalar and integer exponent coordinates. -/

namespace ManuscriptAudit.LaurentUnitProductCoordinates

open LaurentPolynomial

noncomputable section

variable (K : Type) [Field K]

private def monomialUnit (x : Additive Kˣ × ℤ) : (LaurentPolynomial K)ˣ :=
  Units.map (C : K →+* LaurentPolynomial K).toMonoidHom x.1.toMul *
    unitOfInvertible (T x.2 : LaurentPolynomial K)

private theorem coe_monomialUnit (x : Additive Kˣ × ℤ) :
    (monomialUnit K x : LaurentPolynomial K) = C (x.1.toMul : K) * T x.2 := rfl

private def monomialMap : Additive Kˣ × ℤ →+ Additive (LaurentPolynomial K)ˣ where
  toFun x := Additive.ofMul (monomialUnit K x)
  map_zero' := by
    apply Additive.ext
    apply Units.ext
    change (monomialUnit K 0 : LaurentPolynomial K) = 1
    rw [coe_monomialUnit]
    change C (1 : K) * T 0 = 1
    simp
  map_add' a b := by
    apply Additive.ext
    apply Units.ext
    change (monomialUnit K (a + b) : LaurentPolynomial K) =
      (monomialUnit K a : LaurentPolynomial K) * (monomialUnit K b : LaurentPolynomial K)
    simp only [coe_monomialUnit]
    change C ((a.1.toMul : K) * (b.1.toMul : K)) * T (a.2 + b.2) =
      (C (a.1.toMul : K) * T a.2) * (C (b.1.toMul : K) * T b.2)
    rw [map_mul, T_add, mul_mul_mul_comm]

private theorem monomialMap_bijective : Function.Bijective (monomialMap K) := by
  constructor
  · intro a b hab
    have h := congrArg (fun v : Additive (LaurentPolynomial K)ˣ =>
      (v.toMul : LaurentPolynomial K)) hab
    change (monomialUnit K a : LaurentPolynomial K) =
      (monomialUnit K b : LaurentPolynomial K) at h
    rw [coe_monomialUnit, coe_monomialUnit, ← single_eq_C_mul_T, ← single_eq_C_mul_T] at h
    have hTest := congrArg (fun f : LaurentPolynomial K => f.coeff b.2) h
    have hExponent : a.2 = b.2 := by
      by_contra hne
      have hzero : (0 : K) = (b.1.toMul : K) := by
        simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne,
          if_true] using hTest
      exact b.1.toMul.ne_zero hzero.symm
    have hScalar : (a.1.toMul : K) = (b.1.toMul : K) := by
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos hExponent,
        if_true] using hTest
    exact Prod.ext (Additive.ext (Units.ext hScalar)) hExponent
  · intro u
    obtain ⟨a, n, ha, hu⟩ :=
      (LaurentUnits.laurent_isUnit_iff_monomial K (u.toMul : LaurentPolynomial K)).mp u.toMul.isUnit
    refine ⟨(Additive.ofMul ha.unit, n), Additive.ext (Units.ext ?_)⟩
    change (monomialUnit K _ : LaurentPolynomial K) = (u.toMul : LaurentPolynomial K)
    rw [coe_monomialUnit]
    exact (congrArg (fun t : K => C t * T n) ha.unit_spec).trans hu.symm

def unitCoordinates : (Additive Kˣ × ℤ) ≃+ Additive (LaurentPolynomial K)ˣ :=
  AddEquiv.ofBijective (monomialMap K) (monomialMap_bijective K)

theorem unitCoordinates_apply (a : Additive Kˣ) (n : ℤ) :
    ((unitCoordinates K (a, n)).toMul : LaurentPolynomial K) = C (a.toMul : K) * T n :=
  coe_monomialUnit K (a, n)

end
end ManuscriptAudit.LaurentUnitProductCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.LaurentUnitProductCoordinates.unitCoordinates,
      ``ManuscriptAudit.LaurentUnitProductCoordinates.unitCoordinates_apply] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
