import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.LinearCombination

/-! Integer coordinates, trace, and norm in the Eisenstein subring of ℂ. -/

namespace ManuscriptAudit.ComplexEisensteinCoordinates

noncomputable section

theorem primitive_quadratic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 2 + ζ + 1 = 0 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    calc
      _ = ζ ^ 3 - 1 := by ring
      _ = _ := by rw [hζ.pow_eq_one, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hζ.ne_one (by decide)))

/-- The integer span of 1 and a primitive cube root is a subring. -/
def eisensteinSubring (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) : Subring ℂ where
  carrier := {w | ∃ a b : ℤ, w = (a : ℂ) + (b : ℂ) * ζ}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination ((b : ℂ) * (d : ℂ)) * primitive_quadratic hζ
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring

theorem root_mem {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : ζ ∈ eisensteinSubring ζ hζ :=
  ⟨0, 1, by simp⟩

theorem primitive_conj {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : (starRingEnd ℂ) ζ = ζ ^ 2 := by
  have hz : ζ ≠ 0 := by
    intro h
    have hp := hζ.pow_eq_one
    simp [h] at hp
  apply mul_left_cancel₀ hz
  calc
    _ = 1 := by rw [Complex.mul_conj', hζ.norm'_eq_one (by decide)]; simp
    _ = _ := by rw [← pow_succ', hζ.pow_eq_one]

theorem trace_coordinates {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ζ) + (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * ζ) =
      ((2 * a - b : ℤ) : ℂ) := by
  simp only [map_add, map_mul, map_intCast, primitive_conj hζ]
  push_cast
  linear_combination (b : ℂ) * primitive_quadratic hζ

theorem norm_coordinates {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ζ) * (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * ζ) =
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℂ) := by
  simp only [map_add, map_mul, map_intCast, primitive_conj hζ]
  push_cast
  have hs : ζ + ζ ^ 2 = -1 := by linear_combination primitive_quadratic hζ
  calc
    _ = (a : ℂ) ^ 2 + (a : ℂ) * (b : ℂ) * (ζ + ζ ^ 2) + (b : ℂ) ^ 2 * ζ ^ 3 := by ring
    _ = _ := by rw [hs, hζ.pow_eq_one]; ring

end
end ManuscriptAudit.ComplexEisensteinCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ComplexEisensteinCoordinates.eisensteinSubring,
      ``ManuscriptAudit.ComplexEisensteinCoordinates.primitive_conj,
      ``ManuscriptAudit.ComplexEisensteinCoordinates.trace_coordinates,
      ``ManuscriptAudit.ComplexEisensteinCoordinates.norm_coordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
