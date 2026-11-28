import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsDiagonal
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsPositiveSpectrum

/-! The original Hilbert form domain has an orthonormal basis induced by the actual
spectral resolution. Its image is the square-root weighted coordinate space. -/

namespace ManuscriptAudit.Paper10FriedrichsDomainSpectrum

open Paper10FriedrichsResolvent Paper10FriedrichsCompact
open Paper10FriedrichsDiagonal Paper10FriedrichsPositiveSpectrum
open scoped RealInnerProductSpace InnerProductSpace

noncomputable section

variable {D H I : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (hJ : DenseRange J) (hInj : Function.Injective J)
variable (b : HilbertBasis I ℝ H) (e : I → ℝ)
variable (he : ∀ i, (b i, e i • b i) ∈ (realization J).graph)

include hJ he in
theorem positive_label (i : I) : 0 < e i := by
  apply eigenvalue_pos J hJ _ (he i)
  intro h
  have hn := b.orthonormal.norm_eq_one i
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- The Hilbert space of the form has a basis with coordinates given by square roots of
the actual positive energies times the ambient spectral coefficients. -/
include hJ hInj he in
theorem exists_form_basis :
    ∃ d : HilbertBasis I ℝ D, ∀ u i, d.repr u i = Real.sqrt (e i) * b.repr (J u) i := by
  classical
  let v (i : I) : D := Real.sqrt (e i) • J.adjoint (b i)
  have hv (i : I) (u : D) : ⟪v i,u⟫ = Real.sqrt (e i) * b.repr (J u) i := by
    rw [b.repr_apply_apply]
    change ⟪Real.sqrt (e i) • J.adjoint (b i),u⟫ = _
    rw [real_inner_smul_left, J.adjoint_inner_left]
  have hvInner (i j : I) :
      ⟪v i,v j⟫ = Real.sqrt (e i) * Real.sqrt (e j) *
        (e i)⁻¹ * ⟪b i,b j⟫ := by
    have hr := (eigenvector_reciprocity J hJ (e i) (label_ne_zero J hJ b e he i)
      (b i)).mp (he i)
    change ⟪Real.sqrt (e i) • J.adjoint (b i), Real.sqrt (e j) • J.adjoint (b j)⟫ = _
    rw [real_inner_smul_left, real_inner_smul_right, J.adjoint_inner_right]
    change Real.sqrt (e i) * (Real.sqrt (e j) * ⟪resolvent J (b i),b j⟫) = _
    rw [hr, real_inner_smul_left]
    ring
  have hOrtho : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hvInner, (orthonormal_iff_ite.mp b.orthonormal i j)]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, mul_one, ← pow_two, Real.sq_sqrt (positive_label J hJ b e he i).le]
      exact mul_inv_cancel₀ (label_ne_zero J hJ b e he i)
    · rw [if_neg hij, mul_zero]
  have hOrth : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro u hu
    have hz (i : I) : ⟪v i,u⟫ = 0 :=
      (Submodule.mem_orthogonal _ u).mp hu (v i) (Submodule.subset_span ⟨i, rfl⟩)
    have hc (i : I) : b.repr (J u) i = 0 := by
      have h := hz i
      rw [hv] at h
      exact (mul_eq_zero.mp h).resolve_left
        (Real.sqrt_pos.mpr (positive_label J hJ b e he i)).ne'
    rw [Submodule.mem_bot]
    apply hInj
    rw [map_zero]
    apply b.repr.injective
    rw [map_zero]
    apply lp.ext
    funext i
    exact hc i
  have hTotal : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    rw [Submodule.topologicalClosure_eq_top_iff.mpr hOrth]
  refine ⟨HilbertBasis.mk hOrtho hTotal, fun u i => ?_⟩
  rw [HilbertBasis.repr_apply_apply, congrFun (HilbertBasis.coe_mk hOrtho hTotal) i]
  exact hv i u

/-- Ambient vectors belong to the form domain precisely when multiplication by the
square roots of the positive energy labels gives an ℓ² sequence. -/
include hJ hInj he in
theorem range_iff_memℓp (x : H) :
    x ∈ Set.range J ↔ Memℓp (fun i => Real.sqrt (e i) * b.repr x i) 2 := by
  obtain ⟨d, hd⟩ := exists_form_basis J hJ hInj b e he
  constructor
  · rintro ⟨u, rfl⟩
    have h : (fun i => Real.sqrt (e i) * b.repr (J u) i) = fun i => d.repr u i :=
      funext (fun i => (hd u i).symm)
    rw [h]
    exact (d.repr u).property
  · intro h
    let w : lp (fun _ : I => ℝ) 2 := ⟨_, h⟩
    let u := d.repr.symm w
    have hu : d.repr u = w := d.repr.apply_symm_apply w
    refine ⟨u, b.repr.injective ?_⟩
    apply lp.ext
    funext i
    have hc := hd u i
    rw [hu] at hc
    change Real.sqrt (e i) * b.repr x i = Real.sqrt (e i) * b.repr (J u) i at hc
    exact mul_left_cancel₀ (Real.sqrt_pos.mpr (positive_label J hJ b e he i)).ne' hc.symm

end
end ManuscriptAudit.Paper10FriedrichsDomainSpectrum

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsDomainSpectrum.exists_form_basis,
      ``ManuscriptAudit.Paper10FriedrichsDomainSpectrum.range_iff_memℓp] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
