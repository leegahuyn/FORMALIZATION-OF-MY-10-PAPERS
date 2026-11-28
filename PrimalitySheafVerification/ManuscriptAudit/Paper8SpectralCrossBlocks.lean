import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Group an exact Hilbert expansion by eigenvalue, preserving absolute summability. -/

namespace ManuscriptAudit.Paper8SpectralCrossBlocks

open scoped ENNReal InnerProductSpace

noncomputable section

variable {H I Λ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def crossSpectralBlock (b : HilbertBasis I ℂ H) (label : I → Λ) (x y : H) (λ : Λ) : ℂ :=
  ∑' i : {i // label i = λ}, ⟪x, b i.1⟫_ℂ * ⟪b i.1, y⟫_ℂ

theorem summable_norm_basis_cross (b : HilbertBasis I ℂ H) (x y : H) :
    Summable (fun i => ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖) := by
  have hp : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  have h := lp.summable_mul hp (b.repr x) (b.repr y)
  refine h.congr fun i => ?_
  rw [b.repr_apply_apply x i, b.repr_apply_apply y i, norm_mul,
    ← inner_conj_symm x (b i), norm_star]

theorem summable_norm_crossSpectralBlock (b : HilbertBasis I ℂ H) (label : I → Λ) (x y : H) :
    Summable (fun λ => ‖crossSpectralBlock b label x y λ‖) := by
  let e := Equiv.sigmaFiberEquiv label
  have hNorm : Summable (fun p : Σ λ, {i // label i = λ} =>
      ‖⟪x, b (e p)⟫_ℂ * ⟪b (e p), y⟫_ℂ‖) :=
    (summable_norm_basis_cross b x y).comp_injective e.injective
  have hMajorant : Summable (fun λ => ∑' i : {i // label i = λ},
      ‖⟪x, b i.1⟫_ℂ * ⟪b i.1, y⟫_ℂ‖) :=
    hNorm.sigma' (fun λ => hNorm.sigma_factor λ)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun λ => ?_) hMajorant
  exact norm_tsum_le_tsum_norm (hNorm.sigma_factor λ)

theorem tsum_crossSpectralBlock_eq_inner (b : HilbertBasis I ℂ H) (label : I → Λ) (x y : H) :
    (∑' λ, crossSpectralBlock b label x y λ) = ⟪x, y⟫_ℂ := by
  let e := Equiv.sigmaFiberEquiv label
  let f (i : I) := ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ
  have hSum : Summable (fun p : Σ λ, {i // label i = λ} => f (e p)) :=
    (b.summable_inner_mul_inner x y).comp_injective e.injective
  calc
    _ = ∑' p : Σ λ, {i // label i = λ}, f (e p) := hSum.tsum_sigma.symm
    _ = ∑' i : I, f i := e.tsum_eq f
    _ = _ := b.tsum_inner_mul_inner x y

theorem exists_nonzero_crossSpectralBlock (b : HilbertBasis I ℂ H) (label : I → Λ) {x y : H}
    (hxy : ⟪x, y⟫_ℂ ≠ 0) : ∃ λ, crossSpectralBlock b label x y λ ≠ 0 := by
  by_contra! hAll
  apply hxy
  rw [← tsum_crossSpectralBlock_eq_inner b label x y]
  simp only [hAll, tsum_zero]

end
end ManuscriptAudit.Paper8SpectralCrossBlocks

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SpectralCrossBlocks.summable_norm_crossSpectralBlock,
      ``ManuscriptAudit.Paper8SpectralCrossBlocks.exists_nonzero_crossSpectralBlock] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
