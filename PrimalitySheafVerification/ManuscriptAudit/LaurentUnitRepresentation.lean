import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent

/-!
The Laurent polynomial algebra represents the units of a commutative algebra.
The equivalence sends an algebra homomorphism to the image of the invertible
generator and is natural in the target algebra.
-/

namespace ManuscriptAudit.LaurentUnitRepresentation

open LaurentPolynomial

noncomputable section

variable (K R : Type*) [CommSemiring K] [CommSemiring R] [Algebra K R]

private def generatorUnit : (LaurentPolynomial K)ˣ :=
  unitOfInvertible (T 1 : LaurentPolynomial K)

private def evalUnit (u : Rˣ) : LaurentPolynomial K →ₐ[K] R where
  __ := eval₂ (algebraMap K R) u
  commutes' c := by
    rw [← LaurentPolynomial.C_eq_algebraMap]
    exact LaurentPolynomial.eval₂_C (algebraMap K R) u c

private theorem evalUnit_T (u : Rˣ) :
    evalUnit K R u (T 1) = (u : R) := by
  change eval₂ (algebraMap K R) u (T 1) = (u : R)
  simp only [eval₂_T, zpow_one]

private theorem hom_ext_T {f g : LaurentPolynomial K →ₐ[K] R}
    (h : f (T 1) = g (T 1)) : f = g := by
  have he : f.comp (Polynomial.toLaurentAlg : Polynomial K →ₐ[K] LaurentPolynomial K) =
      g.comp Polynomial.toLaurentAlg := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X] using h
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial K))
  apply RingHom.ext
  intro p
  exact AlgHom.congr_fun he p

/-- Maps out of the Laurent polynomial algebra correspond to units. -/
def laurentAlgHomEquivUnits : (LaurentPolynomial K →ₐ[K] R) ≃ Rˣ where
  toFun f := Units.map f.toRingHom.toMonoidHom (generatorUnit K)
  invFun := evalUnit K R
  left_inv f := (hom_ext_T K R) (evalUnit_T K R _)
  right_inv u := Units.ext (evalUnit_T K R u)

/-- The forward map evaluates at the Laurent generator. -/
theorem laurentAlgHomEquivUnits_val (f : LaurentPolynomial K →ₐ[K] R) :
    ↑(laurentAlgHomEquivUnits K R f) = f (T 1) :=
  rfl

/-- The inverse sends a unit to evaluation at that unit. -/
theorem laurentAlgHomEquivUnits_symm_apply (u : Rˣ) (f : LaurentPolynomial K) :
    (laurentAlgHomEquivUnits K R).symm u f = eval₂ (algebraMap K R) u f :=
  rfl

/-- Postcomposition of algebra homomorphisms agrees with mapping units. -/
theorem laurentAlgHomEquivUnits_natural {S : Type*} [CommSemiring S] [Algebra K S]
    (g : R →ₐ[K] S) (f : LaurentPolynomial K →ₐ[K] R) :
    laurentAlgHomEquivUnits K S (g.comp f) =
      Units.map g.toRingHom.toMonoidHom (laurentAlgHomEquivUnits K R f) := by
  apply Units.ext
  rfl

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``laurentAlgHomEquivUnits, ``laurentAlgHomEquivUnits_val,
      ``laurentAlgHomEquivUnits_symm_apply, ``laurentAlgHomEquivUnits_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.LaurentUnitRepresentation
