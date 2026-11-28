import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Star
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! The pointwise sesquilinear Green identity for the actual weight −1/2 connection. -/

namespace ManuscriptAudit.Paper8OddMaassCovariantGreen

open MaassLaplacian

noncomputable section

def coordinateCovariantX (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) * partialX F x y + (Complex.I / 4) * F x y

def coordinateCovariantY (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) * partialY F x y

def coordinateHorizontalFlux (F G : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (starRingEnd ℂ) (G x y) * (partialX F x y + (Complex.I / (4 * (y : ℂ))) * F x y)

def coordinateVerticalFlux (F G : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (starRingEnd ℂ) (G x y) * partialY F x y

theorem coordinate_covariant_green_identity {F G : ℝ → ℝ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hFx : DifferentiableAt ℝ (fun t => F t y) x)
    (hFxx : DifferentiableAt ℝ (fun t => partialX F t y) x)
    (hFyy : DifferentiableAt ℝ (fun t => partialY F x t) y)
    (hGx : DifferentiableAt ℝ (fun t => G t y) x)
    (hGy : DifferentiableAt ℝ (fun t => G x t) y) :
    (y : ℂ) ^ 2 * (partialX (coordinateHorizontalFlux F G) x y +
      partialY (coordinateVerticalFlux F G) x y) =
      (starRingEnd ℂ) (coordinateCovariantX G x y) * coordinateCovariantX F x y +
      (starRingEnd ℂ) (coordinateCovariantY G x y) * coordinateCovariantY F x y -
      (starRingEnd ℂ) (G x y) * (maassDelta (-1 / 2) F x y + (1 / 16 : ℂ) * F x y) := by
  let c := Complex.I / (4 * (y : ℂ))
  have hX : partialX (coordinateHorizontalFlux F G) x y =
      (starRingEnd ℂ) (partialX G x y) * (partialX F x y + c * F x y) +
      (starRingEnd ℂ) (G x y) * (partialX (partialX F) x y + c * partialX F x y) := by
    have hG' : HasDerivAt (fun t => (starRingEnd ℂ) (G t y)) ((starRingEnd ℂ) (partialX G x y)) x :=
      hGx.hasDerivAt.star
    have hF' : HasDerivAt (fun t => partialX F t y + c * F t y)
        (partialX (partialX F) x y + c * partialX F x y) x :=
      hFxx.hasDerivAt.add (hFx.hasDerivAt.const_mul c)
    exact (hG'.mul hF').deriv
  have hY : partialY (coordinateVerticalFlux F G) x y =
      (starRingEnd ℂ) (partialY G x y) * partialY F x y +
      (starRingEnd ℂ) (G x y) * partialY (partialY F) x y := by
    have hG' : HasDerivAt (fun t => (starRingEnd ℂ) (G x t)) ((starRingEnd ℂ) (partialY G x y)) y :=
      hGy.hasDerivAt.star
    exact (hG'.mul hFyy.hasDerivAt).deriv
  have hCX : (starRingEnd ℂ) (coordinateCovariantX G x y) =
      (y : ℂ) * (starRingEnd ℂ) (partialX G x y) - (Complex.I / 4) * (starRingEnd ℂ) (G x y) := by
    unfold coordinateCovariantX
    simp only [map_add, map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hCY : (starRingEnd ℂ) (coordinateCovariantY G x y) =
      (y : ℂ) * (starRingEnd ℂ) (partialY G x y) := by
    unfold coordinateCovariantY
    rw [map_mul, Complex.conj_ofReal]
  have hy₀ : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [hX, hY, hCX, hCY]
  unfold c coordinateCovariantX coordinateCovariantY maassDelta
  push_cast
  field_simp [hy₀] <;> try ring_nf
  all_goals simp [Complex.I_sq] <;> ring

end
end ManuscriptAudit.Paper8OddMaassCovariantGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCovariantGreen.coordinate_covariant_green_identity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
