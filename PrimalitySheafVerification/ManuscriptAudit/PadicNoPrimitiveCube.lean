import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! The two coefficient fields used in Paper 5 contain no primitive cubic root. -/

namespace ManuscriptAudit.PadicNoPrimitiveCube

open scoped Padic

variable (l : ℕ) [Fact l.Prime]

/-- A quadratic cubic-root equation would give a root in every finite residue ring. -/
theorem no_root_of_residue (n : ℕ) (hR : ∀ z : ZMod (l ^ n), z ^ 2 + z + 1 ≠ 0)
    (u : ℚ_[l]) : u ^ 2 + u + 1 ≠ 0 := by
  intro h
  have hCube : u ^ 3 = 1 := by linear_combination (u - 1) * h
  have hNorm : ‖u‖ ^ 3 = 1 := by simpa only [norm_pow, norm_one] using congrArg norm hCube
  have hLe : ‖u‖ ≤ 1 := by
    by_contra! hlt
    have h' : (1 : ℝ) ^ 3 < ‖u‖ ^ 3 := by gcongr <;> norm_num
    rw [hNorm] at h'
    norm_num at h'
  let z : ℤ_[l] := ⟨u, hLe⟩
  have hz : z ^ 2 + z + 1 = 0 := by
    apply Subtype.coe_injective
    change (((z ^ 2 + z + 1 : ℤ_[l]) : ℚ_[l])) = ((0 : ℤ_[l]) : ℚ_[l])
    push_cast
    exact h
  let f := PadicInt.toZModPow n
  have he := congrArg f hz
  simp only [map_add, map_pow, map_one, map_zero] at he
  exact hR (f z) he

/-- Neither the 2-adic nor the 3-adic field has a root of X²+X+1. -/
theorem no_root (hl : l = 2 ∨ l = 3) (u : ℚ_[l]) : u ^ 2 + u + 1 ≠ 0 := by
  rcases hl with rfl | rfl
  · exact no_root_of_residue 2 1 (by decide) u
  · exact no_root_of_residue 3 2 (by decide) u

/-- An Eisenstein integer with nonzero primitive-cube coefficient cannot be a scalar
root in either native p-adic coefficient ring. -/
theorem no_scalar_root (hl : l = 2 ∨ l = 3) (a b : ℤ) (hb : b ≠ 0)
    (r : ℤ_[l]) :
    r ^ 2 - ((2 * a - b : ℤ) : ℤ_[l]) * r + ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) ≠ 0 := by
  intro h
  let x : ℚ_[l] := r
  have hQ := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) h
  push_cast at hQ
  have hB : (b : ℚ_[l]) ≠ 0 := Int.cast_ne_zero.mpr hb
  apply no_root l hl ((x - a) / b)
  field_simp [hB]
  change x ^ 2 - (2 * (a : ℚ_[l]) - b) * x + ((a : ℚ_[l]) ^ 2 - a * b + (b : ℚ_[l]) ^ 2) = 0 at hQ
  linear_combination hQ

end ManuscriptAudit.PadicNoPrimitiveCube

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.PadicNoPrimitiveCube.no_root_of_residue,
      ``ManuscriptAudit.PadicNoPrimitiveCube.no_root,
      ``ManuscriptAudit.PadicNoPrimitiveCube.no_scalar_root] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
