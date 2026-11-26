import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Ring

/-!
# Trace and fixed vectors in dimension two over F₂

The determinant of an automorphism is the unique nonzero scalar.
In dimension two, expansion of det(F - I) identifies it with trace.
-/

namespace ManuscriptAudit.FrobeniusModTwoLinear

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem scalar_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem scalar_eq_of_zero_iff (a b : ZMod 2) (h : a = 0 ↔ b = 0) : a = b := by
  rcases scalar_zero_or_one a with ha | ha
  · exact ha.trans (h.mp ha).symm
  · rcases scalar_zero_or_one b with hb | hb
    · exact (h.mpr hb).trans hb.symm
    · exact ha.trans hb.symm

theorem neg_scalar_eq_self (a : ZMod 2) : -a = a := by
  rcases scalar_zero_or_one a with h | h
  · rw [h, neg_zero]
  · rw [h] <;> decide

private theorem det_sub_one_expansion (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    (M - 1).det = M.det - M.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.one_apply] <;> ring

theorem matrix_det_sub_one_eq_trace (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h : M.det = 1) :
    (M - 1).det = M.trace := by
  rw [det_sub_one_expansion, h]
  calc
    1 - M.trace + 1 = (1 + 1 : ZMod 2) + -M.trace := by ring
    _ = M.trace := by rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_add, neg_scalar_eq_self]

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]

/-- Every F₂-linear automorphism has determinant 1. -/
theorem det_eq_one (F : V ≃ₗ[ZMod 2] V) : LinearMap.det F.toLinearMap = 1 :=
  (scalar_zero_or_one _).resolve_left (LinearEquiv.isUnit_det' F).ne_zero

/-- In dimension two the actual determinant of F minus identity is the actual trace. -/
theorem det_sub_id_eq_trace (b : Module.Basis (Fin 2) (ZMod 2) V) (F : V ≃ₗ[ZMod 2] V) :
    LinearMap.det (F.toLinearMap - LinearMap.id) = LinearMap.trace (ZMod 2) V F.toLinearMap := by
  have hM : (LinearMap.toMatrix b b F.toLinearMap).det = 1 :=
    (LinearMap.det_toMatrix b _).trans (det_eq_one V F)
  rw [← LinearMap.det_toMatrix b, LinearMap.trace_eq_matrix_trace (ZMod 2) b,
    map_sub, LinearMap.toMatrix_id]
  exact matrix_det_sub_one_eq_trace _ hM

/-- Trace zero detects an actual nonzero fixed vector. -/
theorem trace_zero_iff_nonzero_fixed (b : Module.Basis (Fin 2) (ZMod 2) V)
    (F : V ≃ₗ[ZMod 2] V) :
    LinearMap.trace (ZMod 2) V F.toLinearMap = 0 ↔ ∃ v : V, v ≠ 0 ∧ F v = v := by
  letI : Module.Finite (ZMod 2) V := Module.Finite.of_basis b
  rw [← det_sub_id_eq_trace V b F, LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hn⟩
    exact ⟨v, hn, sub_eq_zero.mp (show F v - v = 0 from hv)⟩
  · rintro ⟨v, hn, hv⟩
    exact ⟨v, show F v - v = 0 from sub_eq_zero.mpr hv, hn⟩

/-- The four-element module has the required genuine finite-dimensional basis. -/
def basisOfCardFour [Finite V] (hV : Nat.card V = 4) : Module.Basis (Fin 2) (ZMod 2) V := by
  have hTwo : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [hV, hTwo] at hpow
  have hp : Function.Injective (fun n : ℕ => 2 ^ n) := Nat.pow_right_injective (by decide)
  have hdim : Module.finrank (ZMod 2) V = 2 := hp hpow.symm
  exact Module.finBasisOfFinrankEq hdim

end

end ManuscriptAudit.FrobeniusModTwoLinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.FrobeniusModTwoLinear.det_eq_one,
      ``ManuscriptAudit.FrobeniusModTwoLinear.det_sub_id_eq_trace,
      ``ManuscriptAudit.FrobeniusModTwoLinear.trace_zero_iff_nonzero_fixed,
      ``ManuscriptAudit.FrobeniusModTwoLinear.basisOfCardFour] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
