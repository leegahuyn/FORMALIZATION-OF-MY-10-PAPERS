import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ThetaChosenQuotientAnalysis
import PrimalitySheafVerification.ManuscriptAudit.ThetaWeightedModeAnalysis

/-! The printed sign of the half-weight operator gives a negative quotient quadratic form. -/

namespace ManuscriptAudit.Paper9PrintedLaplacianSign

open MeasureTheory
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open MaassLaplacian ThetaGlobalSection ThetaChosenQuotientAnalysis ThetaWeightedModeAnalysis
open ThetaProfileGenerators
open scoped UpperHalfPlane Pointwise MatrixGroups

noncomputable section

abbrev thetaCoordinates : ℝ → ℝ → ℂ := weighted (1 / 4) jacobiTheta

def printedL (F : ℝ → ℝ → ℂ) (z : ℍ) : ℂ :=
  -maassDelta (1 / 2) F z.re z.im

theorem printedL_theta (z : ℍ) :
    printedL thetaCoordinates z = ((-(3 / 16) : ℝ) : ℂ) * thetaWeightedMode z := by
  rw [printedL, thetaWeightedMode_delta]
  push_cast
  ring

theorem printedL_theta_equivariant (γ : LiteralCuspTruncation.GammaTwo) (z : ℍ) :
    printedL thetaCoordinates (γ • z) =
      thetaUnitaryFactor γ z * printedL thetaCoordinates z := by
  rw [printedL_theta, printedL_theta, thetaWeightedMode_equivariant]
  ring

private theorem theta_integrableOn (D : GammaTwoFundamentalDomain) :
    IntegrableOn (fun z : ℍ => ‖thetaWeightedMode z‖ ^ (2 : ℕ)) D.carrier hyperbolicMeasure := by
  have hOrbit : AEMeasurable gammaTwoQuotientMk
      (hyperbolicMeasure.restrict D.carrier) := measurable_quotient_mk''.aemeasurable
  have h := quotientDensity_integrable D
  have h' := (integrable_map_measure h.aestronglyMeasurable hOrbit).mp h
  simpa only [Function.comp_def, quotientDensity_pullback] using h'

theorem printedL_theta_square_integrable (D : GammaTwoFundamentalDomain) :
    IntegrableOn (fun z : ℍ => ‖printedL thetaCoordinates z‖ ^ (2 : ℕ))
      D.carrier hyperbolicMeasure := by
  have h := (theta_integrableOn D).const_mul (‖((-(3 / 16) : ℝ) : ℂ)‖ ^ (2 : ℕ))
  simpa only [printedL_theta, norm_mul, mul_pow] using h

def thetaQuadraticDensity (q : GammaTwoQuotient) : ℝ :=
  -(3 / 16) * quotientDensity q

theorem thetaQuadraticDensity_pullback (z : ℍ) :
    thetaQuadraticDensity (gammaTwoQuotientMk z) =
      (printedL thetaCoordinates z * (starRingEnd ℂ) (thetaWeightedMode z)).re := by
  rw [thetaQuadraticDensity, quotientDensity_pullback, printedL_theta,
    mul_assoc, Complex.mul_conj, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem printed_L_negative_quadratic_form (D : GammaTwoFundamentalDomain) :
    (∫ q, thetaQuadraticDensity q ∂D.quotientMeasure) < 0 := by
  change (∫ q, -(3 / 16 : ℝ) * quotientDensity q ∂D.quotientMeasure) < 0
  rw [integral_const_mul]
  exact mul_neg_of_neg_of_pos (by norm_num) (quotientDensity_integral_pos D)

theorem printed_L_shifted_homogeneous_solution (z : ℍ) :
    printedL thetaCoordinates z + (3 / 16 : ℂ) * thetaWeightedMode z = 0 := by
  rw [printedL_theta]
  push_cast
  ring

end
end ManuscriptAudit.Paper9PrintedLaplacianSign

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.printedL_theta,
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.printedL_theta_equivariant,
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.printedL_theta_square_integrable,
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.thetaQuadraticDensity_pullback,
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.printed_L_negative_quadratic_form,
      ``ManuscriptAudit.Paper9PrintedLaplacianSign.printed_L_shifted_homogeneous_solution] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
