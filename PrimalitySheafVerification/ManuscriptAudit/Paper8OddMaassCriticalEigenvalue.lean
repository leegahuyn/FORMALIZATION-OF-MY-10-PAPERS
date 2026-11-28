import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassSmoothFactorization
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCriticalVanishing

/-! Genuine level-four odd Maass eigenfunctions at the critical eta eigenvalue vanish. -/

namespace ManuscriptAudit.Paper8OddMaassCriticalEigenvalue

open MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8EtaCriticalOddVanishing Paper8MaassCriticalHolomorphic
open Paper8OddMaassSmoothFactorization Paper8OddGlobalCriticalVanishing Paper8OddGlobalCutoffEnergy
open scoped ENNReal

theorem odd_maass_critical_eigenfunction_eq_zero {F : ℂ → ℂ}
    (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (hEigen : ∀ x y : ℝ, 0 < y →
      maassDelta (-1 / 2) (realProfile F) x y = (3 / 16 : ℂ) * realProfile F x y)
    (hMass : (∫⁻ z in levelFourCells, Paper8MaassStripFubini.normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, F z = 0 :=
  odd_critical_form_eq_zero_of_global_mass (G := raisedField F) hLaw
    (hF.of_le (by norm_num)) (raisedField_differentiableAt hF) (raisedField_realProfile hF)
    (critical_raisedField_adjoint hF hEigen) hMass

end ManuscriptAudit.Paper8OddMaassCriticalEigenvalue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCriticalEigenvalue.odd_maass_critical_eigenfunction_eq_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
