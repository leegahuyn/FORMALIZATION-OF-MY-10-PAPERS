import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsEigenbasis
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsShift

/-! Diagonalization of the actual real unbounded operator, including its
domain, rather than just its action on individual eigenvectors. -/

namespace ManuscriptAudit.Paper10FriedrichsDiagonal

open Paper10FriedrichsResolvent Paper10FriedrichsCompact Paper10FriedrichsShift
open scoped RealInnerProductSpace

noncomputable section

variable {D H I : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (hJ : DenseRange J)
variable (b : HilbertBasis I ℝ H) (e : I → ℝ)
variable (he : ∀ i, (b i, e i • b i) ∈ (realization J).graph)

theorem label_ne_zero (i : I) : e i ≠ 0 := by
  intro h
  have hi := (realization_graph_iff J hJ _ _).mp (he i)
  rw [h, zero_smul, map_zero] at hi
  have hn := b.orthonormal.1 i
  rw [← hi, norm_zero] at hn
  exact zero_ne_one hn

theorem repr_resolvent (y : H) (i : I) :
    b.repr (resolvent J y) i = (e i)⁻¹ * b.repr y i := by
  have hi := (eigenvector_reciprocity J hJ (e i) (label_ne_zero J hJ b e he i)
    (b i)).mp (he i)
  rw [b.repr_apply_apply, b.repr_apply_apply, ← resolvent_symmetric J, hi,
    real_inner_smul_left]

/-- The whole graph of the positive realization is the graph of multiplication by its
eigenvalues in Hilbert coordinates. -/
theorem graph_iff_repr (x y : H) :
    (x, y) ∈ (realization J).graph ↔ ∀ i, b.repr y i = e i * b.repr x i := by
  rw [realization_graph_iff J hJ]
  constructor
  · intro h i
    have hi := repr_resolvent J hJ b e he y i
    rw [h] at hi
    rw [hi, ← mul_assoc, mul_inv_cancel₀ (label_ne_zero J hJ b e he i), one_mul]
  · intro h
    apply b.repr.injective
    ext i
    rw [repr_resolvent J hJ b e he, h, ← mul_assoc,
      inv_mul_cancel₀ (label_ne_zero J hJ b e he i), one_mul]

/-- Removing the real shift subtracts the same scalar from every coordinate of
the full graph. -/
theorem unshifted_graph_iff_repr (c : ℝ) (x y : H) :
    (x, y) ∈ (unshifted J c).graph ↔
      ∀ i, b.repr y i = (e i - c) * b.repr x i := by
  rw [unshifted_graph_iff, graph_iff_repr J hJ b e he]
  constructor
  · intro h i
    have hi := h i
    have ha : b.repr (y + c • x) i = b.repr y i + c * b.repr x i := by
      simp only [map_add, map_smul]
      rfl
    rw [ha] at hi
    rw [sub_mul]
    exact eq_sub_of_add_eq hi
  · intro h i
    have ha : b.repr (y + c • x) i = b.repr y i + c * b.repr x i := by
      simp only [map_add, map_smul]
      rfl
    rw [ha, h i, sub_mul, sub_add_cancel]

/-- Membership in the actual operator domain is exactly square summability of the
weighted spectral coefficients. -/
theorem unshifted_domain_iff_memℓp (c : ℝ) (x : H) :
    x ∈ (unshifted J c).domain ↔ Memℓp (fun i => (e i - c) * b.repr x i) 2 := by
  change (∃ y, (x, y) ∈ (unshifted J c).graph) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    have h := (unshifted_graph_iff_repr J hJ b e he c x y).mp hy
    have f : (fun i => (e i-c) * b.repr x i) = fun i => b.repr y i :=
      funext (fun i => (h i).symm)
    rw [f]
    exact (b.repr y).property
  · intro h
    let w : lp (fun _ : I => ℝ) 2 := ⟨_, h⟩
    refine ⟨b.repr.symm w, (unshifted_graph_iff_repr J hJ b e he c x _).mpr ?_⟩
    intro i
    rw [b.repr.apply_symm_apply]
    rfl

end
end ManuscriptAudit.Paper10FriedrichsDiagonal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsDiagonal.repr_resolvent,
      ``ManuscriptAudit.Paper10FriedrichsDiagonal.graph_iff_repr,
      ``ManuscriptAudit.Paper10FriedrichsDiagonal.unshifted_graph_iff_repr,
      ``ManuscriptAudit.Paper10FriedrichsDiagonal.unshifted_domain_iff_memℓp] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
