import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Energy dissipation in the chosen Hilbert metric

Physical p. 488, equation (4.21). Along a differentiable path driven by a
mobility operator, the derivative is its quadratic form on the Riesz
gradient. The norm-square law characterizes identity mobility among
self-adjoint mobilities.
-/

namespace ManuscriptAudit.Paper10HilbertEnergyDissipation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem energy_derivative_of_mobility (K : H →L[ℝ] H) (g : H)
    {E : H → ℝ} {u : ℝ → H} {D : H →L[ℝ] ℝ} {t : ℝ}
    (hE : HasFDerivAt E D (u t)) (hR : ∀ v, D v = inner ℝ g v)
    (hu : HasDerivAt u (-(K g)) t) :
    HasDerivAt (fun s => E (u s)) (-(inner ℝ g (K g))) t := by
  have h := hE.comp_hasDerivAt t hu
  change HasDerivAt (fun s => E (u s)) (D (-(K g))) t at h
  rw [hR, inner_neg_right] at h
  exact h

theorem nonnegative_mobility_dissipates_energy (K : H →L[ℝ] H) (g : H)
    {E : H → ℝ} {u : ℝ → H} {D : H →L[ℝ] ℝ} {t : ℝ}
    (hE : HasFDerivAt E D (u t)) (hR : ∀ v, D v = inner ℝ g v)
    (hu : HasDerivAt u (-(K g)) t) (hK : 0 ≤ inner ℝ g (K g)) :
    ∃ d : ℝ, HasDerivAt (fun s => E (u s)) d t ∧ d ≤ 0 :=
  ⟨_, energy_derivative_of_mobility K g hE hR hu, neg_nonpos.mpr hK⟩

theorem hilbert_gradient_norm_square (g : H)
    {E : H → ℝ} {u : ℝ → H} {D : H →L[ℝ] ℝ} {t : ℝ}
    (hE : HasFDerivAt E D (u t)) (hR : ∀ v, D v = inner ℝ g v)
    (hu : HasDerivAt u (-g) t) :
    HasDerivAt (fun s => E (u s)) (-(‖g‖^2)) t := by
  simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
    energy_derivative_of_mobility (ContinuousLinearMap.id ℝ H) g hE hR hu

theorem norm_square_for_all_gradients_iff (K : H →L[ℝ] H)
    (hSym : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) :
    (∀ x, inner ℝ x (K x) = ‖x‖^2) ↔ K = ContinuousLinearMap.id ℝ H := by
  constructor
  · intro h
    have hDiag (x : H) : inner ℝ x (K x) = inner ℝ x x :=
      (h x).trans (real_inner_self_eq_norm_sq x).symm
    have hPair (x y : H) : inner ℝ x (K y) = inner ℝ x y := by
      have hCross : inner ℝ y (K x) = inner ℝ x (K y) := by
        rw [← hSym x y, real_inner_comm]
      have hxy : inner ℝ y x = inner ℝ x y := by rw [real_inner_comm]
      have ha := hDiag (x + y)
      simp only [map_add, inner_add_left, inner_add_right, hCross, hxy,
        hDiag x, hDiag y] at ha
      linarith
    ext y
    change K y = y
    let e := K y - y
    have he : inner ℝ e e = 0 := by
      change inner ℝ e (K y - y) = 0
      rw [inner_sub_right, hPair e y, sub_self]
    have hnorm : ‖e‖^2 = 0 := (real_inner_self_eq_norm_sq e).symm.trans he
    have hzero : e = 0 := by
      by_contra hne
      exact (sq_pos_of_pos (norm_pos_iff.mpr hne)).ne' hnorm
    exact sub_eq_zero.mp hzero
  · rintro rfl x
    exact real_inner_self_eq_norm_sq x

end ManuscriptAudit.Paper10HilbertEnergyDissipation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10HilbertEnergyDissipation.energy_derivative_of_mobility,
      ``ManuscriptAudit.Paper10HilbertEnergyDissipation.nonnegative_mobility_dissipates_energy,
      ``ManuscriptAudit.Paper10HilbertEnergyDissipation.hilbert_gradient_norm_square,
      ``ManuscriptAudit.Paper10HilbertEnergyDissipation.norm_square_for_all_gradients_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
