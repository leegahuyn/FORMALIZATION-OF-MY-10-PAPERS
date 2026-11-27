import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportCyclicTransitions
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicInverseLimit

/-! Ordinary additive inverse limits of the finite compact cohomology groups of the actual nodal curves. -/

namespace ManuscriptAudit.NodalCompactSupportCyclicInverseLimit

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineOpen projectiveNode)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalCompactSupportCyclicTransitions
open OpenEtaleCyclicInverseLimit (compatibleClasses padicEquiv)
open OpenEtaleCoefficientReduction (reductionH)

noncomputable section

set_option backward.isDefEq.respectTransparency false
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
local instance power_cast_neZero (r : ℕ) : NeZero ((ℓ ^ r : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero r (NeZero.ne (ℓ : K))⟩

/-- Actual compatible classes on the proper nodal curve, with its identity compactification. -/
abbrev properInverseLimit (n : ℕ) := compatibleClasses (𝟙 (projectiveNode K)) ℓ n

/-- Actual compatible classes on the affine nodal chart in the proper curve. -/
abbrev affineInverseLimit (n : ℕ) := compatibleClasses (affineOpen K) ℓ n

/-- Actual compatible classes on the relative smooth open of the proper curve. -/
abbrev smoothInverseLimit (n : ℕ) := compatibleClasses (smoothOpen K).ι ℓ n

private theorem proper_onto (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n ≤ 2) (r : ℕ) :
    Function.Surjective (reductionH (𝟙 (projectiveNode K)) (ℓ ^ r) ℓ n) := by
  have hr := proper_reductions_surjective K (ℓ ^ r) ℓ h2
  have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact hr.1
  · exact hr.2.1
  · exact hr.2.2

private theorem affine_onto (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n = 1 ∨ n = 2) (r : ℕ) :
    Function.Surjective (reductionH (affineOpen K) (ℓ ^ r) ℓ n) := by
  have hr := affine_reductions_surjective K (ℓ ^ r) ℓ h2
  rcases hn with rfl | rfl
  · exact hr.1
  · exact hr.2

private theorem smooth_onto (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n = 1 ∨ n = 2) (r : ℕ) :
    Function.Surjective (reductionH (smoothOpen K).ι (ℓ ^ r) ℓ n) := by
  have hr := smooth_reductions_surjective K (ℓ ^ r) ℓ h2
  rcases hn with rfl | rfl
  · exact hr.1
  · exact hr.2

/-- The ordinary compact inverse limit of the proper curve is additively ℤℓ in degrees zero, one and two. -/
def properEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n ≤ 2) : properInverseLimit K ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (𝟙 (projectiveNode K)) ℓ n (proper_onto K ℓ h2 n hn)
    (fun r ↦ (NodalCompactSupportCyclicDegrees.properEquiv K (ℓ ^ r) h2 n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

/-- The ordinary compact inverse limit of the affine node is additively ℤℓ in degrees one and two. -/
def affineEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    affineInverseLimit K ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (affineOpen K) ℓ n (affine_onto K ℓ h2 n hn)
    (fun r ↦ (NodalCompactSupportCyclicDegrees.affineEquiv K (ℓ ^ r) h2 n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

/-- The ordinary compact inverse limit of the actual smooth open is additively ℤℓ in degrees one and two. -/
def smoothEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    smoothInverseLimit K ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (smoothOpen K).ι ℓ n (smooth_onto K ℓ h2 n hn)
    (fun r ↦ (NodalCompactSupportCyclicDegrees.smoothEquiv K (ℓ ^ r) h2 n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

end
end ManuscriptAudit.NodalCompactSupportCyclicInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportCyclicInverseLimit.properEquiv,
      ``ManuscriptAudit.NodalCompactSupportCyclicInverseLimit.affineEquiv,
      ``ManuscriptAudit.NodalCompactSupportCyclicInverseLimit.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
