import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspCanonicalTower
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTowerComparison

/-! Classical compact section-tower cohomology of the literal cusp geometric fibres. -/

namespace ManuscriptAudit.IntegralCuspClassicalAdicCohomology

open AlgebraicGeometry CategoryTheory
open IntegralCuspGeometricFiber (affineCompactOpen smoothCompactOpen)
open IntegralCuspCanonicalTower (product_differences_onto affineLimitEquiv smoothLimitEquiv omittedLimits)
open OpenEtaleSectionTower (sectionsFiber)
open OpenEtaleSectionTowerComparison (cohomologyEquiv negative_subsingleton)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]

abbrev affine (n : ℤ) := (sectionsFiber (affineCompactOpen p) ℓ).homology n
abbrev smooth (n : ℤ) := (sectionsFiber (smoothCompactOpen p) ℓ).homology n

/-- The literal affine cusp has ℤℓ in compact degree two in the classical model. -/
def affineTwoEquiv (hℓp : ℓ ≠ p) : affine p ℓ 2 ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (affineCompactOpen p) ℓ
    (fun n ↦ (product_differences_onto p ℓ hℓp n).1) 2).trans (affineLimitEquiv p ℓ hℓp)

/-- The actual smooth open has ℤℓ in compact degrees one and two in the classical model. -/
def smoothEquiv (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) : smooth p ℓ n ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (smoothCompactOpen p) ℓ
    (fun m ↦ (product_differences_onto p ℓ hℓp m).2) n).trans (smoothLimitEquiv p ℓ hℓp n hn)

private theorem transferZero {B D : Type} [AddCommGroup B] [AddCommGroup D]
    (e : B ≃+ D) (h : Subsingleton D) : Subsingleton B :=
  ⟨fun x y ↦ e.injective (h.elim (e x) (e y))⟩

/-- All other nonnegative degrees vanish on the actual cusp affine and smooth models. -/
theorem omitted (hℓp : ℓ ≠ p) (n : ℕ) :
    (n ≠ 2 → Subsingleton (affine p ℓ n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (smooth p ℓ n)) := by
  obtain ⟨hA, hS⟩ := omittedLimits p ℓ hℓp n
  exact ⟨fun h ↦ transferZero (cohomologyEquiv (affineCompactOpen p) ℓ
      (fun m ↦ (product_differences_onto p ℓ hℓp m).1) n) (hA h),
    fun h ↦ transferZero (cohomologyEquiv (smoothCompactOpen p) ℓ
      (fun m ↦ (product_differences_onto p ℓ hℓp m).2) n) (hS h)⟩

/-- The affine cusp and its actual smooth open have zero negative cohomology in the classical model. -/
theorem negative (n : ℤ) (hn : n < 0) :
    Subsingleton (affine p ℓ n) ∧ Subsingleton (smooth p ℓ n) :=
  ⟨negative_subsingleton (affineCompactOpen p) ℓ n hn,
    negative_subsingleton (smoothCompactOpen p) ℓ n hn⟩

end
end ManuscriptAudit.IntegralCuspClassicalAdicCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspClassicalAdicCohomology.affineTwoEquiv,
      ``ManuscriptAudit.IntegralCuspClassicalAdicCohomology.smoothEquiv,
      ``ManuscriptAudit.IntegralCuspClassicalAdicCohomology.omitted,
      ``ManuscriptAudit.IntegralCuspClassicalAdicCohomology.negative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
