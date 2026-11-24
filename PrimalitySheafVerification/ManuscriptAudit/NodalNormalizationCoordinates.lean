import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# A projective nodal cubic and its rational parameter

The nodal comparison for Papers 2, 4, 5, and 6 uses
(Y^2 Z = X^2 (X+Z)) and the homogeneous parametrization
([t:u]mapsto[u(t^2-u^2):t(t^2-u^2):u^3]).
This file verifies the actual coordinate equations and the affine inverse.
-/

namespace ManuscriptAudit.NodalCoordinates

theorem nodal_parameter_satisfies_projective_equation {R : Type*} [CommRing R]
    (t u : R) :
    (t * (t ^ 2 - u ^ 2)) ^ 2 * u ^ 3 =
      (u * (t ^ 2 - u ^ 2)) ^ 2 * (u * (t ^ 2 - u ^ 2) + u ^ 3) := by
  ring

theorem nodal_parameter_has_nonzero_coordinate {K : Type*} [Field K]
    {t u : K} (h : t ≠ 0 ∨ u ≠ 0) :
    u * (t ^ 2 - u ^ 2) ≠ 0 ∨ t * (t ^ 2 - u ^ 2) ≠ 0 ∨ u ^ 3 ≠ 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · have ht : t ≠ 0 := h.resolve_right (fun hz => hz rfl)
    exact Or.inr (Or.inl (by simpa using mul_ne_zero ht (pow_ne_zero 2 ht)))
  · exact Or.inr (Or.inr (pow_ne_zero 3 hu))

theorem nodal_affine_preimages_of_node {K : Type*} [Field K] (t : K) :
    (t ^ 2 - 1 = 0 ∧ t * (t ^ 2 - 1) = 0) ↔ t = 1 ∨ t = -1 := by
  constructor
  · rintro ⟨hx, _⟩
    have he : (t - 1) * (t + 1) = t ^ 2 - 1 := by ring
    rw [hx] at he
    rcases mul_eq_zero.mp he with ha | hb
    · exact Or.inl (sub_eq_zero.mp ha)
    · right
      calc
        t = t + 1 - 1 := (add_sub_cancel_right t 1).symm
        _ = -1 := by rw [hb, zero_sub]
  · rintro (rfl | rfl) <;> simp

theorem nodal_affine_inverse_off_node {K : Type*} [Field K] {x y : K}
    (hx : x ≠ 0) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (y / x) ^ 2 - 1 = x ∧ (y / x) * ((y / x) ^ 2 - 1) = y := by
  have ht : (y / x) ^ 2 = x + 1 := by
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero 2 hx)).mpr (h.trans (mul_comm _ _))
  have he : (y / x) ^ 2 - 1 = x := by
    rw [ht, add_sub_cancel_right]
  refine ⟨he, ?_⟩
  rw [he, div_mul_cancel₀ _ hx]

end ManuscriptAudit.NodalCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.NodalCoordinates.nodal_parameter_satisfies_projective_equation,
      ``ManuscriptAudit.NodalCoordinates.nodal_parameter_has_nonzero_coordinate,
      ``ManuscriptAudit.NodalCoordinates.nodal_affine_preimages_of_node,
      ``ManuscriptAudit.NodalCoordinates.nodal_affine_inverse_off_node] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
