import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsDomainSpectrum

/-! The variational eigenvalue cutoff for the actual form domain, using the
orthonormal eigenvectors of its unbounded realization. -/

namespace ManuscriptAudit.Paper10FriedrichsRayleigh

open Paper10FriedrichsResolvent Paper10FriedrichsDomainSpectrum
open scoped RealInnerProductSpace

noncomputable section

variable {D H I : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (hJ : DenseRange J) (hInj : Function.Injective J)
variable (b : HilbertBasis I ℝ H) (e : I → ℝ)
variable (he : ∀ i, (b i, e i • b i) ∈ (realization J).graph)

private theorem norm_hasSum (x : H) :
    HasSum (fun i => (b.repr x i)^2) (‖x‖^2) := by
  have h := b.hasSum_inner_mul_inner x x
  have hEq :
      (fun i => ⟪x,b i⟫ * ⟪b i,x⟫) = (fun i => (b.repr x i)^2) := by
    funext i
    rw [real_inner_comm x (b i), b.repr_apply_apply, pow_two]
  rw [hEq, real_inner_self_eq_norm_sq] at h
  exact h

/-- The true form energy is the sum of the ambient spectral masses with one energy
factor per eigenvector. -/
include hJ hInj he in
theorem form_energy_hasSum (u : D) :
    HasSum (fun i => e i * (b.repr (J u) i)^2) (‖u‖^2) := by
  obtain ⟨d, hd⟩ := exists_form_basis J hJ hInj b e he
  have h := d.hasSum_inner_mul_inner u u
  have hEq :
      (fun i => ⟪u,d i⟫ * ⟪d i,u⟫) = (fun i => e i * (b.repr (J u) i)^2) := by
    funext i
    have hc : ⟪d i,u⟫ = Real.sqrt (e i) * b.repr (J u) i :=
      (d.repr_apply_apply u i).symm.trans (hd u i)
    rw [real_inner_comm u (d i), hc, ← pow_two, mul_pow,
      Real.sq_sqrt (positive_label J hJ b e he i).le]
  rw [hEq, real_inner_self_eq_norm_sq] at h
  exact h

/-- An ambient state with no coordinates below the threshold has at least the threshold
Rayleigh energy. -/
include hJ hInj he in
theorem rayleigh_ge_of_low_coordinates_zero (R : ℝ) (u : D)
    (hZero : ∀ i, e i < R → b.repr (J u) i = 0) :
    R * ‖J u‖^2 ≤ ‖u‖^2 := by
  have hL := (norm_hasSum b (J u)).mul_left R
  have hU := form_energy_hasSum J hJ hInj b e he u
  have hLE (i : I) :
      R * (b.repr (J u) i)^2 ≤ e i * (b.repr (J u) i)^2 := by
    by_cases h : e i < R
    · rw [hZero i h, zero_pow (by decide), mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (le_of_not_gt h) (sq_nonneg _)
  exact le_of_tendsto_of_tendsto hL hU
    (Filter.Eventually.of_forall fun s => Finset.sum_le_sum (fun i _ => hLE i))

/-- Restriction to the low-energy coordinates is injective on every linear subspace
whose nonzero vectors all have strictly lower Rayleigh energy. -/
include hJ hInj he in
theorem exists_injective_low_coordinates (R : ℝ) (W : Submodule ℝ D)
    (hW : ∀ u : W, u ≠ 0 → ‖(u : D)‖^2 < R * ‖J u‖^2) :
    ∃ P : W →ₗ[ℝ] ({i // e i < R} → ℝ), Function.Injective P ∧
      ∀ u i, P u i = b.repr (J u) i.val := by
  let P : W →ₗ[ℝ] ({i // e i < R} → ℝ) :=
    { toFun := fun u i => b.repr (J u) i.val
      map_add' := by
        intro u v
        funext i
        simp only [Submodule.coe_add, map_add]
        rfl
      map_smul' := by
        intro c u
        funext i
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rfl }
  refine ⟨P, LinearMap.ker_eq_bot.mp ?_, fun _ _ => rfl⟩
  refine le_antisymm ?_ bot_le
  intro u hu
  rw [Submodule.mem_bot]
  by_contra hne
  have hp : P u = 0 := LinearMap.mem_ker.mp hu
  have hz : ∀ i, e i < R → b.repr (J u) i = 0 :=
    fun i hi => congrFun hp ⟨i, hi⟩
  exact (not_lt_of_ge (rayleigh_ge_of_low_coordinates_zero J hJ hInj b e he R u hz))
    (hW u hne)

end
end ManuscriptAudit.Paper10FriedrichsRayleigh

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsRayleigh.form_energy_hasSum,
      ``ManuscriptAudit.Paper10FriedrichsRayleigh.rayleigh_ge_of_low_coordinates_zero,
      ``ManuscriptAudit.Paper10FriedrichsRayleigh.exists_injective_low_coordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
