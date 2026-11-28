import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured

/-! Relative power maps on the actual cusp coordinates and their
Laurent overlap. The coefficient field is fixed. -/

namespace ManuscriptAudit.CuspRelativePowerCoordinates

open Polynomial LaurentPolynomial CuspPunctured

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- Substitution of a power of the line parameter preserves the cusp ring. -/
theorem expand_mem_cusp (m : ℕ) (hm : 2 ≤ m) (f : Polynomial K) :
    Polynomial.expand K m f ∈ CuspSubalgebra K := by
  apply (CuspDelta.cusp_mem_iff_coeff_one_zero K _).mpr
  have h : ¬ m ∣ 1 := fun h ↦ by
    have hm' := Nat.dvd_one.mp h
    omega
  exact (Polynomial.coeff_expand (by omega : 0 < m) f 1).trans (if_neg h)

/-- The relative power map on the actual affine cusp ring. -/
def cuspPower (m : ℕ) (hm : 2 ≤ m) : CuspSubalgebra K →ₐ[K] CuspSubalgebra K where
  toRingHom := ((Polynomial.expand K m).toRingHom.comp (CuspSubalgebra K).val.toRingHom).codRestrict
    (CuspSubalgebra K).toSubring (fun f ↦ expand_mem_cusp K m hm f.val)
  commutes' a := by
    apply Subtype.ext
    change Polynomial.expand K m (algebraMap K (Polynomial K) a) = _
    exact (Polynomial.expand K m).commutes a

private def exponentUnit : ℤ →+ Additive (LaurentPolynomial K)ˣ where
  toFun n := Additive.ofMul (unitOfInvertible (LaurentPolynomial.T n : LaurentPolynomial K))
  map_zero' := by
    apply Additive.ext
    apply Units.ext
    exact LaurentPolynomial.T_zero
  map_add' n j := by
    apply Additive.ext
    apply Units.ext
    exact LaurentPolynomial.T_add n j

private theorem exponentUnit_coe (n : ℤ) :
    ((exponentUnit K n).toMul : LaurentPolynomial K) = LaurentPolynomial.T n := rfl

/-- Substitution of a power of the parameter in the actual Laurent ring. -/
def laurentPower (m : ℕ) : LaurentPolynomial K →ₐ[K] LaurentPolynomial K where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C (exponentUnit K (m : ℤ)).toMul
  commutes' a := by
    change LaurentPolynomial.eval₂ LaurentPolynomial.C (exponentUnit K (m : ℤ)).toMul
      (LaurentPolynomial.C a) = LaurentPolynomial.C a
    exact LaurentPolynomial.eval₂_C _ _ _

theorem laurentPower_T (m : ℕ) (n : ℤ) :
    laurentPower K m (LaurentPolynomial.T n) = LaurentPolynomial.T (n * (m : ℤ)) := by
  have h := congrArg (fun z : Additive (LaurentPolynomial K)ˣ ↦
    (z.toMul : LaurentPolynomial K)) ((exponentUnit K).map_zsmul n (m : ℤ))
  change (exponentUnit K (n • (m : ℤ))).toMul.val =
    (((exponentUnit K (m : ℤ)).toMul) ^ n).val at h
  calc
    _ = (((exponentUnit K (m : ℤ)).toMul) ^ n).val :=
      LaurentPolynomial.eval₂_T _ _ n
    _ = (exponentUnit K (n • (m : ℤ))).toMul.val := h.symm
    _ = _ := by rw [exponentUnit_coe, zsmul_eq_mul]

/-- The power map commutes with the infinity chart's Laurent restriction. -/
theorem toLaurent_commutes (m : ℕ) :
    (laurentPower K m).comp (Polynomial.toLaurentAlg (R := K)) =
      (Polynomial.toLaurentAlg (R := K)).comp (Polynomial.expand K m) := by
  apply Polynomial.algHom_ext
  change laurentPower K m (Polynomial.toLaurent (Polynomial.X : Polynomial K)) =
    Polynomial.toLaurent (Polynomial.expand K m Polynomial.X)
  rw [Polynomial.toLaurent_X, Polynomial.expand_X, Polynomial.toLaurent_X_pow, laurentPower_T, one_mul]

private abbrev inverseLaurent : Polynomial K →ₐ[K] LaurentPolynomial K :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

/-- The power map commutes with restriction in the inverse Laurent coordinate. -/
theorem inverseLaurent_commutes (m : ℕ) :
    (laurentPower K m).comp (inverseLaurent K) =
      (inverseLaurent K).comp (Polynomial.expand K m) := by
  apply Polynomial.algHom_ext
  change laurentPower K m (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X : Polynomial K))) =
    LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.expand K m Polynomial.X))
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, laurentPower_T, neg_one_mul,
    Polynomial.expand_X, Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_T]

/-- Applying scalar Frobenius after relative substitution gives
absolute Frobenius on the polynomial normalization. -/
theorem relative_absolute (p : ℕ) [Fact p.Prime] [CharP K p] (f : Polynomial K) :
    Polynomial.map (frobenius K p) (Polynomial.expand K p f) = f ^ p :=
  Polynomial.map_frobenius_expand (R := K) p f

end
end ManuscriptAudit.CuspRelativePowerCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspRelativePowerCoordinates.cuspPower,
      ``ManuscriptAudit.CuspRelativePowerCoordinates.laurentPower_T,
      ``ManuscriptAudit.CuspRelativePowerCoordinates.toLaurent_commutes,
      ``ManuscriptAudit.CuspRelativePowerCoordinates.inverseLaurent_commutes,
      ``ManuscriptAudit.CuspRelativePowerCoordinates.relative_absolute] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
