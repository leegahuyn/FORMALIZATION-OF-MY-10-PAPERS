import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith

/-! The corrected bound applies to eigenvalues distinct from the ground level on the operator domain. -/

namespace ManuscriptAudit.Paper10MatchedSpectralBound

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D N : Submodule ℝ E}

theorem other_eigenvector_orthogonal (H : D →ₗ[ℝ] E)
    (hSym : ∀ u v : D, inner ℝ (H u) (v : E) = inner ℝ (u : E) (H v))
    {groundEnergy μ : ℝ}
    (hGround : ∀ y ∈ N, ∃ u : D, (u : E) = y ∧ H u = groundEnergy • y)
    {x : D} (hx : H x = μ • (x : E)) (hDistinct : μ ≠ groundEnergy) :
    (x : E) ∈ Nᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨u, hu, he⟩ := hGround y hy
  have hh : groundEnergy * inner ℝ y (x : E) = μ * inner ℝ y (x : E) := by
    simpa only [he, hx, hu, real_inner_smul_left, real_inner_smul_right] using hSym u x
  have hz : (groundEnergy-μ) * inner ℝ y (x : E) = 0 := by rw [sub_mul, hh, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hDistinct))

theorem other_eigenvalue_lower_bound (H : D →ₗ[ℝ] E) (mass : D → ℝ)
    (hSym : ∀ u v : D, inner ℝ (H u) (v : E) = inner ℝ (u : E) (H v))
    {α c β groundEnergy μ : ℝ} (hα : 0 ≤ α)
    (hGround : ∀ y ∈ N, ∃ u : D, (u : E) = y ∧ H u = groundEnergy • y)
    (hRS : ∀ u : D, (u : E) ∈ Nᗮ → c * ‖(u : E)‖^2 ≤ mass u)
    (hForm : ∀ u : D, α * mass u + β * ‖(u : E)‖^2 ≤ inner ℝ (u : E) (H u))
    {x : D} (hx : H x = μ • (x : E)) (hx₀ : (x : E) ≠ 0) (hDistinct : μ ≠ groundEnergy) :
    α*c+β ≤ μ ∧ α*c+β-groundEnergy ≤ μ-groundEnergy := by
  have hOrth := other_eigenvector_orthogonal H hSym hGround hx hDistinct
  have h : (α*c+β) * ‖(x : E)‖^2 ≤ μ * ‖(x : E)‖^2 := by
    calc
      (α*c+β) * ‖(x : E)‖^2 = α * (c * ‖(x : E)‖^2) + β * ‖(x : E)‖^2 := by ring
      _ ≤ α * mass x + β * ‖(x : E)‖^2 :=
        add_le_add (mul_le_mul_of_nonneg_left (hRS x hOrth) hα) le_rfl
      _ ≤ inner ℝ (x : E) (H x) := hForm x
      _ = μ * ‖(x : E)‖^2 := by rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hPos : 0 < ‖(x : E)‖^2 := pow_pos (norm_pos_iff.mpr hx₀) _
  have hLower := le_of_mul_le_mul_right h hPos
  exact ⟨hLower, sub_le_sub_right hLower _⟩

end
end ManuscriptAudit.Paper10MatchedSpectralBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10MatchedSpectralBound.other_eigenvector_orthogonal,
      ``ManuscriptAudit.Paper10MatchedSpectralBound.other_eigenvalue_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
