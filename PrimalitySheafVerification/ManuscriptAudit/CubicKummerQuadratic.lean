import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! The centered cubic's symmetric addition and subtraction forms have no common base point. -/

namespace ManuscriptAudit.CubicKummerQuadratic

open WeierstrassCurve FiniteFieldPointCount

noncomputable section

variable {R : Type*} [CommRing R]

/-- Homogeneous coordinates of the symmetric add/sub map for y²=x³+A. -/
def forms (A : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![v 0 ^ 2 - (4 * A) * (v 1 * v 2),
    2 * (v 1 * v 0) + (4 * A) * (v 2 * v 2),
    v 1 ^ 2 - 4 * (v 0 * v 2)]

theorem map_forms {S : Type*} [CommRing S] (f : R →+* S) (A : R) (v : Fin 3 → R) :
    forms (f A) (f ∘ v) = f ∘ forms A v := by
  ext i
  fin_cases i <;> simp [forms, Function.comp_apply, map_ofNat]

variable {K : Type*} [Field K]

/-- The explicit three forms agree exactly with Mathlib's Weierstrass add/sub map. -/
theorem forms_eq_addSubMap (A : K) (v : Fin 3 → K) :
    forms A v = fun i => ((shortCubic (0 : K) A).addSubMap i).eval v := by
  ext i
  fin_cases i <;>
    simp [forms, WeierstrassCurve.addSubMap, shortCubic, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow] <;> ring

/-- Good reduction makes the homogeneous add/sub map basepoint-free. -/
theorem forms_ne_zero (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) {A : K}
    (hA : A ≠ 0) {v : Fin 3 → K} (hv : v ≠ 0) : forms A v ≠ 0 := by
  letI : (shortCubic (0 : K) A).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA)⟩
  rw [forms_eq_addSubMap]
  exact (shortCubic (0 : K) A).addSubMap_ne_zero hv

end

end ManuscriptAudit.CubicKummerQuadratic

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicKummerQuadratic.map_forms,
      ``ManuscriptAudit.CubicKummerQuadratic.forms_eq_addSubMap,
      ``ManuscriptAudit.CubicKummerQuadratic.forms_ne_zero] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
