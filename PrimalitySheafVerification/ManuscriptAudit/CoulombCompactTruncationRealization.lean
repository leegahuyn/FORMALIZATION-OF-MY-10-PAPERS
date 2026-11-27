import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombCompactTruncationForm
import PrimalitySheafVerification.ManuscriptAudit.CoulombQuotientNumericalRange

/-! The quantitative obstruction applies to a partial Hamiltonian on
the actual compactly truncated quotient whenever its domain and
diagonal form agree with the compactly supported tests. -/

namespace ManuscriptAudit.CoulombCompactTruncationRealization

open CoulombCompactTruncationForm CoulombQuotientNumericalRange
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A realization on the compact three-cusp cut has unit expectations
arbitrarily far below zero. -/
theorem truncated_numericalRange_unbounded (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnTruncation D Y r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r) :
    ¬ BddBelow (numericalRange T) := by
  apply numericalRange_unbounded_of_quotient_tests D V hV hB T test
  · intro r hr
    exact (hMass r hr).trans (truncation_integrals_eq D Y hY V r hr).1
  · intro r hr
    obtain ⟨_, hE, hP⟩ := truncation_integrals_eq D Y hY V r hr
    rw [hForm r hr, hE, hP]

/-- In particular a symmetric or self-adjoint realization agreeing with
the stated test form cannot satisfy any quadratic lower bound. -/
theorem truncated_realization_has_no_lower_bound (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnTruncation D Y r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r) :
    ¬ ∃ C : ℝ, ∀ u : T.domain, C * ‖(u : H)‖ ^ 2 ≤ inner ℝ (u : H) (T u) := by
  rintro ⟨C, hC⟩
  apply truncated_numericalRange_unbounded D Y hY V hV hB T test hMass hForm
  refine ⟨C, ?_⟩
  rintro a ⟨u, hu, rfl⟩
  simpa only [hu, one_pow, mul_one] using hC u

end
end ManuscriptAudit.CoulombCompactTruncationRealization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombCompactTruncationRealization.truncated_numericalRange_unbounded,
      ``ManuscriptAudit.CoulombCompactTruncationRealization.truncated_realization_has_no_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
