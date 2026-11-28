import Lean.Util.CollectAxioms
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import PrimalitySheafVerification.ManuscriptAudit.CuspScheme
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured

/-! The integral closure of the true cusp coordinates inside its Laurent
puncture is the polynomial normalization, in every characteristic. -/

namespace ManuscriptAudit.CuspLaurentIntegralClosure

open CuspPunctured (CuspSubalgebra)

noncomputable section

universe u
variable (K : Type u) [Field K]

abbrev A := CuspSubalgebra K
abbrev B := Polynomial K
abbrev L := LaurentPolynomial K
abbrev F := FractionRing (B K)

/-- Algebra structure on the Laurent puncture supplied by the cusp coordinates. -/
instance laurentAlgebra : Algebra (A K) (L K) :=
  ((Polynomial.toLaurent : B K →+* L K).comp (algebraMap (A K) (B K))).toAlgebra

instance laurentScalarTower : IsScalarTower (A K) (B K) (L K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private theorem fraction_X_ne_zero :
    algebraMap (B K) (F K) (Polynomial.X : B K) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (B K) (F K))).mpr Polynomial.X_ne_zero

/-- The Laurent puncture embeds in the polynomial fraction field. -/
def toFraction : L K →ₐ[B K] F K :=
  IsLocalization.Away.liftAlgHom (Polynomial.X : B K) (f := Algebra.ofId (B K) (F K))
    (isUnit_iff_ne_zero.mpr (fraction_X_ne_zero K))

theorem toFraction_injective : Function.Injective (toFraction K) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (Polynomial.X : B K))
    (L K) (toFraction K).toRingHom
  intro b hb
  change toFraction K (algebraMap (B K) (L K) b) = 0 at hb
  rw [AlgHom.commutes] at hb
  have h : b = 0 := (IsFractionRing.injective (B K) (F K)) (hb.trans (map_zero _).symm)
  rw [h, map_zero]

/-- The polynomial functions considered as an algebra over the cusp ring. -/
abbrev polynomialToLaurent : B K →ₐ[A K] L K := Algebra.ofId (B K) (L K) |>.restrictScalars (A K)

private theorem polynomial_isIntegral (b : B K) :
    IsIntegral (A K) (polynomialToLaurent K b) := by
  letI : Module.Finite (A K) (B K) := CuspDelta.paper2_cusp_inclusion_finite K
  letI : Algebra.IsIntegral (A K) (B K) := Algebra.IsIntegral.of_finite _ _
  exact (Algebra.IsIntegral.isIntegral b).map (polynomialToLaurent K)

private theorem polynomial_is_integral_closure :
    IsIntegralClosure (B K) (A K) (F K) := by
  classical
  letI : GCDMonoid (B K) := EuclideanDomain.gcdMonoid _
  letI : Module.Finite (A K) (B K) := CuspDelta.paper2_cusp_inclusion_finite K
  letI : Algebra.IsIntegral (A K) (B K) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegralClosure.of_isIntegrallyClosed (B K) (A K) (F K)

/-- A native polynomial chart for the relative integral closure in the Laurent puncture. -/
def polynomialEquiv : B K ≃ₐ[A K] integralClosure (A K) (L K) := by
  let f := (polynomialToLaurent K).codRestrict _ (polynomial_isIntegral K)
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    exact Polynomial.toLaurent_injective (congrArg Subtype.val h)
  · intro x
    letI := polynomial_is_integral_closure K
    have h : IsIntegral (A K) (toFraction K x.val) :=
      (show IsIntegral (A K) x.val from x.property).map ((toFraction K).restrictScalars (A K))
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B K)).mp h
    refine ⟨b, Subtype.ext ((toFraction_injective K) ?_)⟩
    change toFraction K (algebraMap (B K) (L K) b) = toFraction K x.val
    rw [AlgHom.commutes]
    exact hb

theorem polynomialEquiv_coe (b : B K) :
    (polynomialEquiv K b).val = Polynomial.toLaurent b := rfl

end
end ManuscriptAudit.CuspLaurentIntegralClosure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspLaurentIntegralClosure.polynomialEquiv,
      ``ManuscriptAudit.CuspLaurentIntegralClosure.polynomialEquiv_coe] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
