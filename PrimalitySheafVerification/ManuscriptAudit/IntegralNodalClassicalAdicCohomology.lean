import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalTowerExactness
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTowerComparison

/-! The classical compact section-tower model on the literal geometric fibres of the fixed nodal family. -/

namespace ManuscriptAudit.IntegralNodalClassicalAdicCohomology

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open IntegralNodalGeometricPrimePower (affineCompactifyingOpen)
open OpenEtaleSectionTower (sectionsFiber)
open OpenEtaleSectionTowerComparison (cohomologyEquiv negative_subsingleton)
open IntegralNodalTowerExactness (difference_at_two difference_at_odd limits_at_two_vanish limits_at_odd_vanish)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Cohomology of the actual mapping-cocone model of the proper geometric fibre. -/
abbrev proper (p : ℕ) [Fact p.Prime] (n : ℤ) :=
  (sectionsFiber (𝟙 (geometricFiber p)) ℓ).homology n

/-- Cohomology of the actual mapping-cocone model of the affine geometric chart. -/
abbrev affine (p : ℕ) [Fact p.Prime] (n : ℤ) :=
  (sectionsFiber (affineCompactifyingOpen p) ℓ).homology n

/-- Cohomology of the actual mapping-cocone model of the relative smooth open. -/
abbrev smooth (p : ℕ) [Fact p.Prime] (n : ℤ) :=
  (sectionsFiber (geometricSmoothOpen p).ι ℓ).homology n

/-- The proper fibre at (2) has additive ℤℓ in degrees zero and two in the classical model. -/
def properAtTwo (hℓ₂ : ℓ ≠ 2) (n : ℕ) (hn : n = 0 ∨ n = 2) : proper ℓ 2 n ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (𝟙 (geometricFiber 2)) ℓ
    (fun m ↦ (difference_at_two ℓ hℓ₂ m).1) n).trans
    (IntegralNodalCharacteristicTwoInverseLimit.properEquiv ℓ hℓ₂ n hn)

/-- The literal affine chart at (2) has additive ℤℓ in compact degree two. -/
def affineAtTwo (hℓ₂ : ℓ ≠ 2) : affine ℓ 2 2 ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (affineCompactifyingOpen 2) ℓ
    (fun m ↦ (difference_at_two ℓ hℓ₂ m).2.1) 2).trans
    (IntegralNodalCharacteristicTwoInverseLimit.affineEquiv ℓ hℓ₂)

/-- The actual relative smooth open at (2) has additive ℤℓ in compact degree two. -/
def smoothAtTwo (hℓ₂ : ℓ ≠ 2) : smooth ℓ 2 2 ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (geometricSmoothOpen 2).ι ℓ
    (fun m ↦ (difference_at_two ℓ hℓ₂ m).2.2) 2).trans
    (IntegralNodalCharacteristicTwoInverseLimit.smoothEquiv ℓ hℓ₂)

/-- At an odd residue prime the proper geometric fibre has additive ℤℓ in degrees zero through two. -/
def properAtOdd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p)
    (n : ℕ) (hn : n ≤ 2) : proper ℓ p n ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (𝟙 (geometricFiber p)) ℓ
    (fun m ↦ (difference_at_odd ℓ p hp hℓp m).1) n).trans
    (IntegralNodalGeometricInverseLimit.properEquiv p ℓ hp hℓp n hn)

/-- At an odd residue prime the literal affine chart has additive ℤℓ in compact degrees one and two. -/
def affineAtOdd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p)
    (n : ℕ) (hn : n = 1 ∨ n = 2) : affine ℓ p n ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (affineCompactifyingOpen p) ℓ
    (fun m ↦ (difference_at_odd ℓ p hp hℓp m).2.1) n).trans
    (IntegralNodalGeometricInverseLimit.affineEquiv p ℓ hp hℓp n hn)

/-- At an odd residue prime the actual smooth open has additive ℤℓ in compact degrees one and two. -/
def smoothAtOdd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p)
    (n : ℕ) (hn : n = 1 ∨ n = 2) : smooth ℓ p n ≃+ ℤ_[ℓ] :=
  (cohomologyEquiv (geometricSmoothOpen p).ι ℓ
    (fun m ↦ (difference_at_odd ℓ p hp hℓp m).2.2) n).trans
    (IntegralNodalGeometricInverseLimit.smoothEquiv p ℓ hp hℓp n hn)

private theorem transferZero {B D : Type} [AddCommGroup B] [AddCommGroup D]
    (e : B ≃+ D) (h : Subsingleton D) : Subsingleton B :=
  ⟨fun x y ↦ e.injective (h.elim (e x) (e y))⟩

/-- The remaining nonnegative degrees vanish on the literal fibre at (2). -/
theorem omittedAtTwo (hℓ₂ : ℓ ≠ 2) (n : ℕ) :
    (¬ (n = 0 ∨ n = 2) → Subsingleton (proper ℓ 2 n)) ∧
      (n ≠ 2 → Subsingleton (affine ℓ 2 n)) ∧ (n ≠ 2 → Subsingleton (smooth ℓ 2 n)) := by
  obtain ⟨hP, hA, hS⟩ := limits_at_two_vanish ℓ hℓ₂ n
  exact ⟨fun h ↦ transferZero (cohomologyEquiv (𝟙 (geometricFiber 2)) ℓ
      (fun m ↦ (difference_at_two ℓ hℓ₂ m).1) n) (hP h),
    fun h ↦ transferZero (cohomologyEquiv (affineCompactifyingOpen 2) ℓ
      (fun m ↦ (difference_at_two ℓ hℓ₂ m).2.1) n) (hA h),
    fun h ↦ transferZero (cohomologyEquiv (geometricSmoothOpen 2).ι ℓ
      (fun m ↦ (difference_at_two ℓ hℓ₂ m).2.2) n) (hS h)⟩

/-- The remaining nonnegative degrees vanish on each odd residue prime's literal geometric fibre. -/
theorem omittedAtOdd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) :
    (¬ n ≤ 2 → Subsingleton (proper ℓ p n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (affine ℓ p n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (smooth ℓ p n)) := by
  obtain ⟨hP, hA, hS⟩ := limits_at_odd_vanish ℓ p hp hℓp n
  exact ⟨fun h ↦ transferZero (cohomologyEquiv (𝟙 (geometricFiber p)) ℓ
      (fun m ↦ (difference_at_odd ℓ p hp hℓp m).1) n) (hP h),
    fun h ↦ transferZero (cohomologyEquiv (affineCompactifyingOpen p) ℓ
      (fun m ↦ (difference_at_odd ℓ p hp hℓp m).2.1) n) (hA h),
    fun h ↦ transferZero (cohomologyEquiv (geometricSmoothOpen p).ι ℓ
      (fun m ↦ (difference_at_odd ℓ p hp hℓp m).2.2) n) (hS h)⟩

/-- All negative degrees vanish on each of the three displayed classical compact models. -/
theorem negative (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : n < 0) :
    Subsingleton (proper ℓ p n) ∧ Subsingleton (affine ℓ p n) ∧ Subsingleton (smooth ℓ p n) :=
  ⟨negative_subsingleton (𝟙 (geometricFiber p)) ℓ n hn,
    negative_subsingleton (affineCompactifyingOpen p) ℓ n hn,
    negative_subsingleton (geometricSmoothOpen p).ι ℓ n hn⟩

end
end ManuscriptAudit.IntegralNodalClassicalAdicCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.properAtTwo,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.affineAtTwo,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.smoothAtTwo,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.properAtOdd,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.affineAtOdd,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.smoothAtOdd,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.omittedAtTwo,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.omittedAtOdd,
      ``ManuscriptAudit.IntegralNodalClassicalAdicCohomology.negative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
