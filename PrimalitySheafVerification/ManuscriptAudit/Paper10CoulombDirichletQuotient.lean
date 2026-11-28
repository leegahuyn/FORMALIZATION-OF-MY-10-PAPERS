import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombDirichletMode
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-! The Dirichlet projection counterexample descends to the genuine width-two
infinity cusp of the Gamma(2) orbit quotient. -/

namespace ManuscriptAudit.Paper10CoulombDirichletQuotient

open LiteralCuspTruncation (OrbitQuotient orbitPoint)
open Paper10CoulombMultiplier (codifferential)
open Paper10CoulombDirichletMode
open SmoothGaugeCurvature (partialX partialY)
open scoped UpperHalfPlane

noncomputable section

private abbrev E := ℝ × ((ℝ × ℝ) × (ℝ × ℝ))

private def values (z : ℍ) : E :=
  (potential z.re z.im, Paper10CoulombDirichletMode.residual z.re z.im, inputForm z.re z.im)

private theorem same_on_high_orbit {z w : ℍ} (hz : 1 < z.im) (hw : 1 < w.im)
    (h : orbitPoint w = orbitPoint z) : values w = values z := by
  obtain ⟨m, hm⟩ := (HighInfinityCusp.high_orbitPoint_eq_iff_even_translate le_rfl hz hw).mp h
  have hx : w.re = z.re + 2 * (m : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hm
  have hy : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hm
  obtain ⟨hφ, hb, ha⟩ := periodic z.re z.im m
  change (potential w.re w.im, Paper10CoulombDirichletMode.residual w.re w.im, inputForm w.re w.im) = _
  rw [hx, hy, hφ, hb, ha]
  rfl

/-- These are the scalar value and the two actual covector components in the
width-two cusp coframe, extended by zero away from the high chart. -/
def dataOnQuotient (q : OrbitQuotient) : E := by
  classical
  exact if h : ∃ z : ℍ, 1 < z.im ∧ orbitPoint z = q then values (Classical.choose h) else 0

theorem values_on_high (z : ℍ) (hz : 1 < z.im) :
    dataOnQuotient (orbitPoint z) = values z := by
  have h : ∃ w : ℍ, 1 < w.im ∧ orbitPoint w = orbitPoint z := ⟨z, hz, rfl⟩
  rw [dataOnQuotient, dif_pos h]
  exact same_on_high_orbit hz (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- Every nonzero input on the quotient lies strictly inside the truncation
at height six. In particular it vanishes in collars around both ends
of the high cusp chart used for the construction. -/
theorem input_inside_truncation (q : OrbitQuotient) (h : (dataOnQuotient q).2.2 ≠ 0) :
    ∃ z : ℍ, orbitPoint z = q ∧ 5 ≤ z.im ∧ z.im ≤ 11/2 := by
  by_cases hh : ∃ z : ℍ, 1 < z.im ∧ orbitPoint z = q
  · let z := Classical.choose hh
    have hz : 1 < z.im ∧ orbitPoint z = q := Classical.choose_spec hh
    rw [← hz.2, values_on_high z hz.1] at h
    have ha : inputForm z.re z.im ≠ (0, 0) := h
    exact ⟨z, hz.2, le_of_not_gt (fun l ↦ ha (zero_below_cusp_band _ _ l).2.2),
      le_of_not_gt (fun l ↦ ha (zero_input_near_boundary _ _ l))⟩
  · exact (h (by simp [dataOnQuotient, hh])).elim

/-- The prescribed scalar Dirichlet correction leaves a nonzero normal
component at the genuine truncation horocycle. -/
theorem boundary_counterexample :
    ∃ z : ℍ, z.im = 6 ∧
      (dataOnQuotient (orbitPoint z)).1 = 0 ∧
      (dataOnQuotient (orbitPoint z)).2.2 = (0, 0) ∧
      (dataOnQuotient (orbitPoint z)).2.1.2 = -1 := by
  let z : ℍ := ⟨⟨1/2, 6⟩, by norm_num⟩
  use z
  rw [values_on_high z (by norm_num [z])]
  exact ⟨rfl, potential_zero_on_boundary _, zero_input_near_boundary _ _ (by norm_num [z]),
    residual_nonzero_on_boundary⟩

theorem prescribed_correction_coclosed (x y : ℝ) :
    codifferential (fun s t ↦ ((inputForm s t).1 - partialX potential s t,
      (inputForm s t).2 - partialY potential s t)) x y = 0 := by
  have h : (fun s t ↦ ((inputForm s t).1 - partialX potential s t,
      (inputForm s t).2 - partialY potential s t)) = Paper10CoulombDirichletMode.residual := by
    funext s t
    exact correction_eq_residual s t
  rw [h]
  exact residual_coclosed x y

end
end ManuscriptAudit.Paper10CoulombDirichletQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombDirichletQuotient.values_on_high,
      ``ManuscriptAudit.Paper10CoulombDirichletQuotient.input_inside_truncation,
      ``ManuscriptAudit.Paper10CoulombDirichletQuotient.boundary_counterexample,
      ``ManuscriptAudit.Paper10CoulombDirichletQuotient.prescribed_correction_coclosed] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
