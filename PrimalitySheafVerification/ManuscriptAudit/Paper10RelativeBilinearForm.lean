import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeFormClosed

/-! The shifted metrics in the relative form theorem come from the two
genuine real symmetric bilinear forms on the common domain. -/

namespace ManuscriptAudit.Paper10RelativeBilinearForm

open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private abbrev Form := D →ₗ[ℝ] D →ₗ[ℝ] ℝ

private def shifted (ι : D →ₗ[ℝ] H) (P : Form (D := D)) (k : ℝ) (x y : D) : ℝ :=
  P x y + k * ⟪ι x, ι y⟫

/-- Realize the shifted bilinear form as a genuine positive definite scalar product. -/
def shiftedCore (ι : D →ₗ[ℝ] H) (hi : Function.Injective ι)
    (P : Form (D := D)) (hP : ∀ x y, P y x = P x y)
    (k c : ℝ) (hc : 0 < c) (h : ∀ x, c * ‖ι x‖ ^ 2 ≤ shifted ι P k x x) :
    InnerProductSpace.Core ℝ D where
  inner := shifted ι P k
  conj_inner_symm x y := by
    change shifted ι P k y x = shifted ι P k x y
    unfold shifted
    rw [hP x y, real_inner_comm (ι x) (ι y)]
  re_inner_nonneg x := by
    change 0 ≤ shifted ι P k x x
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (h x)
  add_left x y z := by
    simp only [shifted, map_add, LinearMap.add_apply, inner_add_left]
    ring
  smul_left x y r := by
    change shifted ι P k (r • x) y = r * shifted ι P k x y
    simp only [shifted, map_smul, LinearMap.smul_apply, smul_eq_mul, real_inner_smul_left]
    ring
  definite x hx := by
    apply hi
    rw [map_zero]
    by_contra hne
    have hpos : 0 < c * ‖ι x‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.mpr hne) 2)
    have hle := h x
    change shifted ι P k x x = 0 at hx
    rw [hx] at hle
    exact (not_lt_of_ge hle) hpos

private theorem dist_sq (P : InnerProductSpace.Core ℝ D) (x y : D) :
    letI := P.toNormedAddCommGroup
    dist x y ^ 2 = P.inner (x - y) (x - y) := by
  letI := P.toNormedAddCommGroup
  rw [dist_eq_norm]
  change Real.sqrt (P.inner (x - y) (x - y)) ^ 2 = _
  exact Real.sq_sqrt (P.re_inner_nonneg _)

variable (ι : D →ₗ[ℝ] H) (hi : Function.Injective ι)
  (Q V : Form (D := D)) (hQ : ∀ x y, Q y x = Q x y) (hV : ∀ x y, V y x = V x y)
  (m a b : ℝ) (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
  (hLower : ∀ x, -m * ‖ι x‖ ^ 2 ≤ Q x x)
  (hPerturb : ∀ x, |V x x| ≤ a * Q x x + b * ‖ι x‖ ^ 2)

def originalCore : InnerProductSpace.Core ℝ D :=
  shiftedCore ι hi Q hQ (m + 1) 1 zero_lt_one (by
    intro x
    rw [shifted, real_inner_self_eq_norm_sq, one_mul]
    nlinarith only [hLower x])

def perturbedCore : InnerProductSpace.Core ℝ D :=
  shiftedCore ι hi (Q + V)
    (fun x y => by simp only [LinearMap.add_apply, hQ x y, hV x y])
    ((1 - a) * (m + 1) + b) (1 - a) (sub_pos.mpr ha) (by
      intro x
      rw [shifted, real_inner_self_eq_norm_sq, LinearMap.add_apply, LinearMap.add_apply]
      have h₁ := (Paper10RelativeFormBounds.shifted_comparison
        (fun x => Q x x) (fun x => V x x) (fun x => ‖ι x‖ ^ 2) m a b
        hm ha₀ hb (fun x => sq_nonneg _) hLower hPerturb x).1
      have h₂ : ‖ι x‖ ^ 2 ≤ Q x x + (m + 1) * ‖ι x‖ ^ 2 := by
        nlinarith only [hLower x]
      exact (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr ha.le)).trans h₁)

/-- The actual shifted norm of the perturbed bilinear form on the original domain
is complete whenever the original form is closed. -/
theorem complete_perturbed
    (hComplete : letI := (originalCore ι hi Q hQ m hLower).toNormedAddCommGroup
      CompleteSpace D) :
    letI := (perturbedCore ι hi Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb).toNormedAddCommGroup
    CompleteSpace D := by
  let E := (originalCore ι hi Q hQ m hLower).toNormedAddCommGroup
  let F := (perturbedCore ι hi Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb).toNormedAddCommGroup
  exact @Paper10RelativeFormClosed.complete_of_relative_bound D D D
    E.toMetricSpace.toPseudoMetricSpace hComplete F.toMetricSpace.toPseudoMetricSpace
    (Equiv.refl D) (fun x y => x - y) (fun x => Q x x) (fun x => V x x)
    (fun x => ‖ι x‖ ^ 2) m a b hm ha₀ ha hb (fun _ => sq_nonneg _) hLower hPerturb
    (fun x y => (dist_sq (originalCore ι hi Q hQ m hLower) x y).trans (by
      change shifted ι Q (m + 1) (x - y) (x - y) = _
      rw [shifted, real_inner_self_eq_norm_sq]))
    (fun x y => (dist_sq (perturbedCore ι hi Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb) x y).trans (by
      change shifted ι (Q + V) _ (x - y) (x - y) = _
      rw [shifted, real_inner_self_eq_norm_sq, LinearMap.add_apply, LinearMap.add_apply]))

end
end ManuscriptAudit.Paper10RelativeBilinearForm

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeBilinearForm.complete_perturbed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
