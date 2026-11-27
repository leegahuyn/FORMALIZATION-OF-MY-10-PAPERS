import Lean.Util.CollectAxioms
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassDerivativeOpen

/-! The native derivative opens cover every scheme point of a smooth Weierstrass model. -/

namespace ManuscriptAudit.Paper2WeierstrassSpectrumCover

open Polynomial WeierstrassCurve Paper2WeierstrassDerivativeOpen

noncomputable section

variable {R F : Type*} [CommRing R] [Field F]

private theorem quotient_eval (W : WeierstrassCurve R)
    (f : W.toAffine.CoordinateRing →+* F) (g : (Polynomial R)[X]) :
    f (AdjoinRoot.mk W.toAffine.polynomial g) =
      g.eval₂ (f.comp (AdjoinRoot.of W.toAffine.polynomial))
        (f (AdjoinRoot.root W.toAffine.polynomial)) := by
  have h : g.eval₂ (AdjoinRoot.of W.toAffine.polynomial)
      (AdjoinRoot.root W.toAffine.polynomial) = AdjoinRoot.mk W.toAffine.polynomial g := by
    rw [← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  rw [← h, Polynomial.hom_eval₂]

/-- A field-valued point of the original quotient has at least one nonzero partial derivative. -/
theorem field_point_nonsingular (W : WeierstrassCurve R) [W.IsElliptic]
    (f : W.toAffine.CoordinateRing →+* F) :
    f (xDerivative W) ≠ 0 ∨ f (yDerivative W) ≠ 0 := by
  let Q := f.comp (AdjoinRoot.of W.toAffine.polynomial)
  let x : F := Q X
  let y : F := f (AdjoinRoot.root W.toAffine.polynomial)
  let c : R →+* F := Q.comp C
  let W' := (W.map c).toAffine
  have hX : Q X = x := rfl
  have hC (r : R) : Q (C r) = c r := rfl
  have hEq : W'.Equation x y := by
    have h := quotient_eval W f W.toAffine.polynomial
    rw [AdjoinRoot.mk_self, map_zero] at h
    change 0 = W.toAffine.polynomial.eval₂ Q y at h
    rw [Affine.equation_iff']
    simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C, map_add, map_mul, map_pow, hX, hC] at h
    change y ^ 2 + (W.map c).a₁ * x * y + (W.map c).a₃ * y -
      (x ^ 3 + (W.map c).a₂ * x ^ 2 + (W.map c).a₄ * x + (W.map c).a₆) = 0
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination -h
  have hN := (Affine.equation_iff_nonsingular (W := W')).mp hEq
  obtain ⟨_, hx | hy⟩ := (Affine.nonsingular_iff' (W := W') x y).mp hN
  · left
    rw [xDerivative, quotient_eval]
    change W.toAffine.polynomialX.eval₂ Q y ≠ 0
    simp only [Affine.polynomialX, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      map_add, map_mul, map_pow, hX, hC]
    simpa only [W', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄, map_ofNat] using hx
  · right
    rw [yDerivative, quotient_eval]
    change W.toAffine.polynomialY.eval₂ Q y ≠ 0
    simp only [Affine.polynomialY, eval₂_add, eval₂_mul, eval₂_X, eval₂_C,
      map_add, map_mul, hX, hC]
    simpa only [W', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_ofNat, add_assoc] using hy

/-- The two genuine principal opens cover the whole prime spectrum. -/
theorem derivative_opens_cover (W : WeierstrassCurve R) [W.IsElliptic] :
    (PrimeSpectrum.basicOpen (xDerivative W) : Set (PrimeSpectrum W.toAffine.CoordinateRing)) ∪
      (PrimeSpectrum.basicOpen (yDerivative W) : Set (PrimeSpectrum W.toAffine.CoordinateRing)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro P
  letI : P.asIdeal.IsPrime := P.isPrime
  let f : W.toAffine.CoordinateRing →+* P.asIdeal.ResidueField := algebraMap _ _
  change P ∈ PrimeSpectrum.basicOpen (xDerivative W) ∨
    P ∈ PrimeSpectrum.basicOpen (yDerivative W)
  simp only [PrimeSpectrum.mem_basicOpen, ← Ideal.algebraMap_residueField_eq_zero]
  exact field_point_nonsingular W f

end
end ManuscriptAudit.Paper2WeierstrassSpectrumCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassSpectrumCover.field_point_nonsingular,
      ``ManuscriptAudit.Paper2WeierstrassSpectrumCover.derivative_opens_cover] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
