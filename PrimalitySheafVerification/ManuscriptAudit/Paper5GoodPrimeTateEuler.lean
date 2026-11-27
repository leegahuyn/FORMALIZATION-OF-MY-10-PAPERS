import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5GoodPrimeTate
import PrimalitySheafVerification.ManuscriptAudit.RankTwoEulerDeterminant
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualAnalyticLocalZeta

/-! The same integral Euler numerator controls the native Tate determinant and the analytic local zeta. -/

namespace ManuscriptAudit.Paper5GoodPrimeTateEuler

open Module Polynomial PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open CubicSplitPrimeTateCoefficients (basis)
open CubicSplitPrimeTateExtensions (relative relative_eq_power)
open Paper5GoodPrimeTate (extensionTrace extension_power_coefficients)
open Paper5ActualHasseWeil (firstTrace)
open Paper5ActualAnalyticLocalZeta (rationalZeta)
open scoped Padic

noncomputable section

def localNumerator (a : ℤ) (q : ℕ) : ℤ[X] :=
  1 - C a * X + C (q : ℤ) * X^2

theorem localNumerator_eval {R : Type*} [CommRing R] (a : ℤ) (q : ℕ) (z : R) :
    (localNumerator a q).eval₂ (Int.castRingHom R) z = 1-(a : R)*z+(q : R)*z^2 := by
  simp [localNumerator]

variable (p : ℕ) [Fact p.Prime]

theorem analytic_local_uses_numerator (A : ZMod p) (z : ℂ) :
    rationalZeta (p : ℂ) (firstTrace p A : ℂ) z =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℂ) z /
        ((1-z)*(1-(p : ℂ)*z)) := by
  simp [rationalZeta, localNumerator_eval, mul_comm]

variable (L D : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
    [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D] [Algebra D L]
    [IsScalarTower (ZMod p) D L]

theorem native_relative_euler_numerator (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) (z : ℤ_[l]) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) -
      z • relative p L D A l) =
      (localNumerator (extensionTrace p D A) (Fintype.card D)).eval₂ (Int.castRingHom ℤ_[l]) z := by
  rw [RankTwoEulerDeterminant.linear_determinant (basis p L hp hA l hl), localNumerator_eval]
  have h := extension_power_coefficients p L D hp hA l hl
  dsimp only at h
  rw [relative_eq_power, h.1, h.2]
  ring

end
end ManuscriptAudit.Paper5GoodPrimeTateEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5GoodPrimeTateEuler.localNumerator_eval,
      ``ManuscriptAudit.Paper5GoodPrimeTateEuler.analytic_local_uses_numerator,
      ``ManuscriptAudit.Paper5GoodPrimeTateEuler.native_relative_euler_numerator] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
