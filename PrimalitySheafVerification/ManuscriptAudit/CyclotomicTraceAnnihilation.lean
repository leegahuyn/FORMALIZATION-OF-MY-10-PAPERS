import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NoncommRing

/-! The trace of an endomorphism conjugating a cubic rotation is killed by three. -/

namespace ManuscriptAudit.CyclotomicTraceAnnihilation

open LinearMap

noncomputable section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

theorem three_times_trace_eq_zero (S F : Module.End R M)
    (hS : S ^ 3 = 1) (hQuad : S ^ 2 + S + 1 = 0)
    (hF : F * S = S ^ 2 * F) :
    (3 : R) * LinearMap.trace R M F = 0 := by
  have h₂ : S ^ 2 * S = 1 := by rw [← pow_succ] <;> exact hS
  have h₃ : S * S ^ 2 = 1 := by rw [← pow_succ'] <;> exact hS
  have hConj : S * F * S ^ 2 = S ^ 2 * F := by
    calc
      _ = S * ((F * S) * S) := by noncomm_ring
      _ = S * ((S ^ 2 * F) * S) := by rw [hF]
      _ = (S * S ^ 2) * (F * S) := by noncomm_ring
      _ = _ := by rw [h₃, one_mul, hF]
  have hTrace₂ : LinearMap.trace R M (S ^ 2 * F) = LinearMap.trace R M F := by
    calc
      _ = LinearMap.trace R M (S * F * S ^ 2) := congrArg (LinearMap.trace R M) hConj.symm
      _ = LinearMap.trace R M (S ^ 2 * (S * F)) := LinearMap.trace_mul_comm R _ _
      _ = LinearMap.trace R M ((S ^ 2 * S) * F) := by rw [mul_assoc]
      _ = _ := by rw [h₂, one_mul]
  have hTrace₁ : LinearMap.trace R M (S * F) = LinearMap.trace R M F := by
    rw [LinearMap.trace_mul_comm, hF, hTrace₂]
  have h := congrArg (fun T : Module.End R M => LinearMap.trace R M (T * F)) hQuad
  change LinearMap.trace R M ((S ^ 2 + S + 1) * F) =
    LinearMap.trace R M ((0 : Module.End R M) * F) at h
  simp only [add_mul, one_mul, zero_mul, map_add, map_zero, hTrace₂, hTrace₁] at h
  calc
    _ = LinearMap.trace R M F + LinearMap.trace R M F + LinearMap.trace R M F := by ring
    _ = _ := h

theorem trace_eq_zero_of_noZeroDivisors [NoZeroDivisors R] (h₃ : (3 : R) ≠ 0)
    (S F : Module.End R M) (hS : S ^ 3 = 1) (hQuad : S ^ 2 + S + 1 = 0)
    (hF : F * S = S ^ 2 * F) : LinearMap.trace R M F = 0 :=
  (mul_eq_zero.mp (three_times_trace_eq_zero R M S F hS hQuad hF)).resolve_left h₃

theorem trace_eq_zero_of_three_unit (h₃ : IsUnit (3 : R))
    (S F : Module.End R M) (hS : S ^ 3 = 1) (hQuad : S ^ 2 + S + 1 = 0)
    (hF : F * S = S ^ 2 * F) : LinearMap.trace R M F = 0 := by
  obtain ⟨u, hu⟩ := h₃
  have h := three_times_trace_eq_zero R M S F hS hQuad hF
  calc
    _ = (↑u⁻¹ : R) * ((3 : R) * LinearMap.trace R M F) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_zero]

end
end ManuscriptAudit.CyclotomicTraceAnnihilation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CyclotomicTraceAnnihilation.three_times_trace_eq_zero,
      ``ManuscriptAudit.CyclotomicTraceAnnihilation.trace_eq_zero_of_noZeroDivisors,
      ``ManuscriptAudit.CyclotomicTraceAnnihilation.trace_eq_zero_of_three_unit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
