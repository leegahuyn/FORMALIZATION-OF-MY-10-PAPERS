import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspSection
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrintedLaplacianSign

/-! The actual extended theta section has the height-profile derivatives in the high cusp. -/

namespace ManuscriptAudit.Paper9HighCuspCoordinates

open Filter Set MaassLaplacian Paper9HighCuspSection Paper9PrintedLaplacianSign
open scoped UpperHalfPlane Topology

noncomputable section

def coordinates (a : ℝ → ℂ) (x y : ℝ) : ℂ :=
  extendedSection a (UpperHalfPlane.ofComplex (complexPoint x y))

private theorem complexPoint_re (x y : ℝ) : (complexPoint x y).re = x := by
  simp [complexPoint, Complex.add_re, Complex.mul_re]

theorem coordinates_at_point (a : ℝ → ℂ) (z : ℍ) :
    coordinates a z.re z.im = extendedSection a z := by
  have he : complexPoint z.re z.im = (z : ℂ) := by
    apply Complex.ext <;> simp [complexPoint_re]
  rw [coordinates, he, UpperHalfPlane.ofComplex_apply]

theorem coordinates_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    coordinates a x y = a y := by
  have hpos : 0 < (complexPoint x y).im := by
    rw [complexPoint_im]
    exact zero_lt_one.trans hy
  unfold coordinates
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  have hh : 1 < (⟨complexPoint x y, hpos⟩ : ℍ).im := by
    change 1 < (complexPoint x y).im
    rwa [complexPoint_im]
  rw [extendedSection_at_high a _ hh]
  change a (complexPoint x y).im = a y
  rw [complexPoint_im]

theorem partialX_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    partialX (coordinates a) x y = 0 := by
  change deriv (fun t => coordinates a t y) x = 0
  simp only [coordinates_high a _ y hy, deriv_const]

theorem partialXX_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    partialX (partialX (coordinates a)) x y = 0 := by
  change deriv (fun t => partialX (coordinates a) t y) x = 0
  simp only [partialX_high a _ y hy, deriv_const]

theorem partialY_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    partialY (coordinates a) x y = deriv a y := by
  change deriv (fun t => coordinates a x t) y = deriv a y
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact coordinates_high a x t ht

theorem partialYY_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    partialY (partialY (coordinates a)) x y = deriv (deriv a) y := by
  change deriv (fun t => partialY (coordinates a) x t) y = deriv (deriv a) y
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact partialY_high a x t ht

theorem printedL_high (a : ℝ → ℂ) (z : ℍ) (hz : 1 < z.im) :
    printedL (coordinates a) z = ((z.im : ℂ) ^ 2) * deriv (deriv a) z.im := by
  unfold printedL maassDelta
  rw [partialXX_high a _ _ hz, partialYY_high a _ _ hz, partialX_high a _ _ hz]
  ring

end
end ManuscriptAudit.Paper9HighCuspCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9HighCuspCoordinates.coordinates_at_point,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.coordinates_high,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.partialX_high,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.partialXX_high,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.partialY_high,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.partialYY_high,
      ``ManuscriptAudit.Paper9HighCuspCoordinates.printedL_high] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
