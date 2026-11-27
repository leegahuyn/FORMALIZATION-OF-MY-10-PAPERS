import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper8CuspRaisingHolomorphic

/-! The coefficient reconstructed from a zero-raising cusp section is holomorphic. -/

namespace ManuscriptAudit.Paper8CuspHolomorphicCoefficient

open Filter Set MaassLaplacian Paper8NegativeHalfMaassFactorization
open Paper8CuspRaisingHolomorphic
open scoped Topology

noncomputable section

def coefficient (F : Profile) (z : ℂ) : ℂ :=
  star (F z.re z.im * (↑((z.im ^ (1/4 : ℝ))⁻¹ : ℝ) : ℂ))

private theorem point_re (x y : ℝ) : (complexPoint x y).re = x := by
  simp [complexPoint, Complex.add_re, Complex.mul_re]

theorem profile_recover (F : Profile) (x y : ℝ) (hy : 0 < y) :
    profile (coefficient F) x y = F x y := by
  have hW : (↑(y ^ (1/4 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hy (1/4 : ℝ)).ne'
  unfold profile coefficient
  rw [point_re, complexPoint_im, star_star, Complex.ofReal_inv]
  field_simp [hW] <;> ring

theorem coefficient_complex_differentiable (F : Profile) (x y : ℝ) (hy : 0 < y)
    (hF : DifferentiableAt ℝ F.uncurry (x, y)) (hRaise : raising F x y = 0) :
    DifferentiableAt ℂ (coefficient F) (complexPoint x y) := by
  let z := complexPoint x y
  have hz : 0 < z.im := by simpa only [z, complexPoint_im] using hy
  have hF' : DifferentiableAt ℝ F.uncurry (z.re, z.im) := by
    simpa only [z, point_re, complexPoint_im] using hF
  have hPair : DifferentiableAt ℝ (fun t : ℂ => (t.re, t.im)) z :=
    (Complex.reCLM.differentiableAt (x := z)).prodMk (Complex.imCLM.differentiableAt (x := z))
  have hA' : DifferentiableAt ℝ (F.uncurry ∘ (fun t : ℂ => (t.re, t.im))) z :=
    hF'.comp z hPair
  have hA : DifferentiableAt ℝ (fun t : ℂ => F t.re t.im) z := hA'
  have hW := ((Real.hasDerivAt_rpow_const (p := (1/4 : ℝ)) (Or.inl hz.ne')).inv
    (Real.rpow_pos_of_pos hz (1/4 : ℝ)).ne').ofReal_comp
  have hB : DifferentiableAt ℝ (fun t : ℂ => (↑((t.im ^ (1/4 : ℝ))⁻¹ : ℝ) : ℂ)) z :=
    hW.differentiableAt.comp z Complex.imCLM.differentiableAt
  have hC : DifferentiableAt ℝ (coefficient F) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hA.mul hB)
  apply raising_eq_zero_implies_complex_differentiable (coefficient F) x y hy hC
  have hx : (fun t => profile (coefficient F) t y) = (fun t => F t y) :=
    funext (fun t => profile_recover F t y hy)
  have hy' : (fun t => profile (coefficient F) x t) =ᶠ[𝓝 y] F x := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact profile_recover F x t ht
  have hxD : partialX (profile (coefficient F)) x y = partialX F x y := by
    unfold partialX
    rw [hx]
  have hyD : partialY (profile (coefficient F)) x y = partialY F x y :=
    hy'.deriv_eq
  unfold raising
  rw [hxD, hyD, profile_recover F x y hy]
  exact hRaise

end
end ManuscriptAudit.Paper8CuspHolomorphicCoefficient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8CuspHolomorphicCoefficient.profile_recover,
      ``ManuscriptAudit.Paper8CuspHolomorphicCoefficient.coefficient_complex_differentiable] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
