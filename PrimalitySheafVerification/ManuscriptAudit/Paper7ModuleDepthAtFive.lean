import Lean.Util.CollectAxioms
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Regular.RegularSequence
import PrimalitySheafVerification.ManuscriptAudit.Paper7KoszulCRTResidue

/-! A one-dimensional regular chart does not force its finite modules
to have depth one. The residue summand gives an actual obstruction. -/

namespace ManuscriptAudit.Paper7ModuleDepthAtFive

open Paper7KoszulCRTBaseChange Paper7KoszulCRTResidue
open RingTheory.Sequence

noncomputable section

abbrev F := R × S

private theorem ring_not_field : ¬ IsField R := by
  intro h
  obtain ⟨a, ha⟩ := h.mul_inv_cancel parameter_ne_zero
  have h₁ : (1 : R) ∈ IsLocalRing.maximalIdeal R := ha ▸
    (IsLocalRing.maximalIdeal R).mul_mem_right a parameter_in_maximal
  have ht : IsLocalRing.maximalIdeal R = ⊤ := by
    apply le_antisymm le_top
    intro x _
    simpa only [mul_one] using (IsLocalRing.maximalIdeal R).mul_mem_left x h₁
  exact (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top ht

theorem ring_dimension_one : ringKrullDim R = 1 := by
  letI : IsDomain R := IsLocalization.isDomain_of_local_atPrime inferInstance
  exact IsPrincipalIdealRing.ringKrullDim_eq_one R ring_not_field

theorem module_dimension_one : Module.supportDim R F = 1 := by
  have hLow := Module.supportDim_le_of_surjective
    (LinearMap.fst R R S) (fun a ↦ ⟨(a, 0), rfl⟩)
  rw [Module.supportDim_self_eq_ringKrullDim, ring_dimension_one] at hLow
  have hHigh := Module.supportDim_le_ringKrullDim R F
  rw [ring_dimension_one] at hHigh
  exact le_antisymm hHigh hLow

theorem parameter_is_regular_for_ring : IsRegular R ([5] : List R) := by
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  · intro x hx
    have he : x = 5 := by simpa using hx
    exact he.symm ▸ parameter_in_maximal
  · exact IsWeaklyRegular.cons (show IsSMulRegular R (5:R) from regular_parameter)
      (IsWeaklyRegular.nil _ _)

/-- All local parameters annihilate the same nonzero residue vector in
the actual finite module. -/
theorem parameter_not_regular_for_module (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) :
    ¬ IsSMulRegular F a := by
  intro h
  have haI : a ∈ I := quotient_ideal_eq_maximal.symm ▸ ha
  have hA : reduction a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have hz : a • ((0, 1) : F) = a • (0 : F) := by
    apply Prod.ext
    · change a * 0 = a * 0
      rfl
    · change reduction a * 1 = reduction a * 0
      rw [hA, zero_mul, zero_mul]
  have e : (1 : S) = 0 := congrArg Prod.snd (h hz)
  exact (one_ne_zero : (1 : ZMod 5) ≠ 0) (by simpa using congrArg crtFieldEquiv e)

/-- The maximum positive length of an actual local regular sequence in
the finite module is zero although its support has dimension one. -/
theorem every_module_regular_length_zero (xs : List R)
    (h : IsRegular F xs) (hx : ∀ a ∈ xs, a ∈ IsLocalRing.maximalIdeal R) :
    xs.length = 0 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      exact (parameter_not_regular_for_module a (hx a (by simp))
        ((isRegular_cons_iff F a xs).mp h).1).elim

end
end ManuscriptAudit.Paper7ModuleDepthAtFive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7ModuleDepthAtFive.ring_dimension_one,
      ``ManuscriptAudit.Paper7ModuleDepthAtFive.module_dimension_one,
      ``ManuscriptAudit.Paper7ModuleDepthAtFive.parameter_is_regular_for_ring,
      ``ManuscriptAudit.Paper7ModuleDepthAtFive.every_module_regular_length_zero] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
