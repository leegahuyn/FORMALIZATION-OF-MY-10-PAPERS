import Lean.Util.CollectAxioms
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-! The actual Laurent algebra with all `ℓ`-power roots of its coordinate.
Its monomials use the additive exponents in the localization of the integers. -/

namespace ManuscriptAudit.LaurentKummerTowerAlgebra

open scoped nonZeroDivisors

noncomputable section

variable (K : Type*) [CommRing K] (ℓ : ℕ)

abbrev Exponent := Localization.Away (ℓ : ℤ)
abbrev Tower := AddMonoidAlgebra K (Exponent ℓ)

private abbrev inverseBase : Exponent ℓ :=
  IsLocalization.Away.invSelf (ℓ : ℤ)

private theorem base_mul_inverse :
    algebraMap ℤ (Exponent ℓ) (ℓ : ℤ) * inverseBase ℓ = 1 :=
  IsLocalization.Away.mul_invSelf (ℓ : ℤ)

/-- The exponent of the compatible Laurent root at level `n`. -/
def rootExponent (n : ℕ) : Exponent ℓ := (inverseBase ℓ) ^ n

theorem rootExponent_succ (n : ℕ) : ℓ • rootExponent ℓ (n + 1) = rootExponent ℓ n := by
  simp only [nsmul_eq_mul, rootExponent]
  have h : (ℓ : Exponent ℓ) * inverseBase ℓ = 1 := by
    simpa only [map_natCast] using base_mul_inverse ℓ
  rw [pow_succ', ← mul_assoc, h, one_mul]

/-- The natural inclusion of the Laurent polynomial algebra. -/
def laurentMap : LaurentPolynomial K →+* Tower K ℓ :=
  AddMonoidAlgebra.mapDomainRingHom K (algebraMap ℤ (Exponent ℓ)).toAddMonoidHom

private def monomial (x : Exponent ℓ) : Tower K ℓ :=
  AddMonoidAlgebra.of K (Exponent ℓ) (Multiplicative.ofAdd x)

private theorem monomial_pow (x : Exponent ℓ) (n : ℕ) :
    monomial K ℓ x ^ n = monomial K ℓ (n • x) :=
  (map_pow (AddMonoidAlgebra.of K (Exponent ℓ)) (Multiplicative.ofAdd x) n).symm

def root (n : ℕ) : Tower K ℓ := monomial K ℓ (rootExponent ℓ n)

theorem root_zero : root K ℓ 0 = laurentMap K ℓ (LaurentPolynomial.T 1) := by
  change monomial K ℓ ((inverseBase ℓ) ^ 0) = laurentMap K ℓ (LaurentPolynomial.T 1)
  rw [pow_zero, monomial, AddMonoidAlgebra.of_apply]
  change AddMonoidAlgebra.single (1 : Exponent ℓ) (1 : K) =
    AddMonoidAlgebra.mapDomain (algebraMap ℤ (Exponent ℓ))
      (AddMonoidAlgebra.single (1 : ℤ) (1 : K))
  rw [AddMonoidAlgebra.mapDomain_single, map_one]

theorem root_succ (n : ℕ) : root K ℓ (n + 1) ^ ℓ = root K ℓ n := by
  change monomial K ℓ (rootExponent ℓ (n + 1)) ^ ℓ = monomial K ℓ (rootExponent ℓ n)
  rw [monomial_pow, rootExponent_succ]

theorem root_power (n : ℕ) : root K ℓ n ^ (ℓ ^ n) = laurentMap K ℓ (LaurentPolynomial.T 1) := by
  induction n with
  | zero => simpa only [pow_zero, pow_one] using root_zero K ℓ
  | succ n h =>
    rw [pow_succ', pow_mul, root_succ, h]

theorem root_isUnit (n : ℕ) : IsUnit (root K ℓ n) :=
  isUnit_of_dvd_one ⟨monomial K ℓ (-rootExponent ℓ n), by
    change 1 = monomial K ℓ (rootExponent ℓ n) * monomial K ℓ (-rootExponent ℓ n)
    simp [monomial, AddMonoidAlgebra.of_apply] <;> rfl⟩

/-- Every exponent comes from a single finite Laurent stage. -/
theorem exponent_from_finite_stage (x : Exponent ℓ) :
    ∃ n : ℕ, ∃ a : ℤ, a • rootExponent ℓ n = x := by
  obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (ℓ : ℤ)) x
  have h₁ : algebraMap ℤ (Exponent ℓ) ((ℓ : ℤ) ^ n) * rootExponent ℓ n = 1 := by
    rw [map_pow, rootExponent, ← mul_pow, base_mul_inverse, one_pow]
  refine ⟨n, a, ?_⟩
  rw [zsmul_eq_mul]
  calc
    _ = (algebraMap ℤ (Exponent ℓ) a) * rootExponent ℓ n := by simp
    _ = (x * algebraMap ℤ (Exponent ℓ) ((ℓ : ℤ) ^ n)) * rootExponent ℓ n := by rw [h]
    _ = _ := by rw [mul_assoc, h₁, mul_one]

end
end ManuscriptAudit.LaurentKummerTowerAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentKummerTowerAlgebra.root_zero,
      ``ManuscriptAudit.LaurentKummerTowerAlgebra.root_succ,
      ``ManuscriptAudit.LaurentKummerTowerAlgebra.root_power,
      ``ManuscriptAudit.LaurentKummerTowerAlgebra.root_isUnit,
      ``ManuscriptAudit.LaurentKummerTowerAlgebra.exponent_from_finite_stage] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
