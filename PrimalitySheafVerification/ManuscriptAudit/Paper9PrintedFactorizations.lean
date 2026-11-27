import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspNegative

/-! Literal raising and lowering expressions and their local high-cusp action. -/

namespace ManuscriptAudit.Paper9PrintedFactorizations

open Filter Set MaassLaplacian Paper9HighCuspCoordinates Paper9HighCuspNegative
open Paper9CuspPotentialForm HyperbolicCuspGaugeTest Paper9PrintedLaplacianSign
open scoped UpperHalfPlane ContDiff Topology

noncomputable section

/-- The printed operator 2i ∂/∂z + k/y in real coordinates. -/
def raise (k : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  Complex.I * partialX F x y + partialY F x y + (k : ℂ) / (y : ℂ) * F x y

/-- The printed operator −2i y² ∂/∂bar(z) in real coordinates. -/
def lower (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  ((y : ℂ) ^ 2) * (-Complex.I * partialX F x y + partialY F x y)

theorem raise_high (k : ℝ) (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    raise k (coordinates a) x y = deriv a y + (k : ℂ) / (y : ℂ) * a y := by
  simp [raise, partialX_high a _ _ hy, partialY_high a _ _ hy, coordinates_high a _ _ hy]

theorem lower_high (a : ℝ → ℂ) (x y : ℝ) (hy : 1 < y) :
    lower (coordinates a) x y = ((y : ℂ) ^ 2) * deriv a y := by
  simp [lower, partialX_high a _ _ hy, partialY_high a _ _ hy]

/-- A compactly supported profile equal to y on the interior of its plateau. -/
def plateauAmplitude (y : ℝ) : ℂ := (y : ℂ) * heightAmplitude 1 y

theorem plateauAmplitude_smooth : ContDiff ℝ ∞ plateauAmplitude :=
  Complex.ofRealCLM.contDiff.mul (heightAmplitude_smooth 1)

theorem plateauAmplitude_zero (y : ℝ) (h : y < 1 + 2 ∨ 1 + 5 < y) :
    plateauAmplitude y = 0 := by
  rw [plateauAmplitude, heightAmplitude_zero 1 y h, mul_zero]

private theorem plateauAmplitude_eq {y : ℝ} (h₁ : 4 < y) (h₂ : y < 5) :
    plateauAmplitude y = (y : ℂ) := by
  rw [plateauAmplitude, heightAmplitude, heightTest,
    cuspBump_one_on_middle (by linarith) (by linarith), Complex.ofReal_one, mul_one]

private def testHeight : ℝ := 9 / 2

private theorem testHeight_high : 1 < testHeight := by norm_num [testHeight]

private theorem plateauAmplitude_near :
    plateauAmplitude =ᶠ[𝓝 testHeight] (fun y : ℝ => (y : ℂ)) := by
  filter_upwards [Ioo_mem_nhds (show 4 < testHeight by norm_num [testHeight])
    (show testHeight < 5 by norm_num [testHeight])] with y hy
  exact plateauAmplitude_eq hy.1 hy.2

private theorem realCast_deriv (y : ℝ) : deriv (fun t : ℝ => (t : ℂ)) y = 1 := by
  simpa only [id_eq, Complex.ofReal_one] using ((hasDerivAt_id y).ofReal_comp).deriv

private theorem plateauDeriv_near : deriv plateauAmplitude =ᶠ[𝓝 testHeight] (fun _ => 1) :=
  plateauAmplitude_near.deriv.mono fun y hy => hy.trans (realCast_deriv y)

private theorem raise_near (k x : ℝ) :
    raise k (coordinates plateauAmplitude) x =ᶠ[𝓝 testHeight] (fun _ => 1 + (k : ℂ)) := by
  filter_upwards [plateauAmplitude_near, plateauDeriv_near, Ioi_mem_nhds testHeight_high] with y ha hd hy
  rw [raise_high _ _ _ _ hy, ha, hd]
  have hzero : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy).ne'
  rw [div_mul_cancel₀ _ hzero]

private theorem lower_near (x : ℝ) :
    lower (coordinates plateauAmplitude) x =ᶠ[𝓝 testHeight] (fun y : ℝ => (y : ℂ) ^ 2) := by
  filter_upwards [plateauDeriv_near, Ioi_mem_nhds testHeight_high] with y hd hy
  rw [lower_high _ _ _ hy, hd, mul_one]

private theorem raise_partialX (k x : ℝ) :
    partialX (raise k (coordinates plateauAmplitude)) x testHeight = 0 := by
  change deriv (fun t => raise k (coordinates plateauAmplitude) t testHeight) x = 0
  rw [funext fun t => (raise_near k t).eq_of_nhds]
  simp

private theorem lower_partialX (x : ℝ) :
    partialX (lower (coordinates plateauAmplitude)) x testHeight = 0 := by
  change deriv (fun t => lower (coordinates plateauAmplitude) t testHeight) x = 0
  rw [funext fun t => (lower_near t).eq_of_nhds]
  simp

private theorem raise_partialY (k x : ℝ) :
    partialY (raise k (coordinates plateauAmplitude)) x testHeight = 0 := by
  simpa only [partialY, deriv_const] using (raise_near k x).deriv_eq

private theorem lower_partialY (x : ℝ) :
    partialY (lower (coordinates plateauAmplitude)) x testHeight = 2 * (testHeight : ℂ) := by
  have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) testHeight := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id testHeight).ofReal_comp
  have hpow := (hcast.pow 2).deriv
  change deriv (lower (coordinates plateauAmplitude) x) testHeight = _
  rw [(lower_near x).deriv_eq]
  simpa using hpow

def testPoint : ℍ :=
  ⟨complexPoint 0 testHeight, by rw [complexPoint_im]; exact zero_lt_one.trans testHeight_high⟩

private theorem testPoint_im : testPoint.im = testHeight := complexPoint_im _ _

theorem printedL_plateau : printedL (coordinates plateauAmplitude) testPoint = 0 := by
  have hz : 1 < testPoint.im := by rw [testPoint_im]; exact testHeight_high
  have hD : deriv (deriv plateauAmplitude) testHeight = 0 := by
    simpa only [deriv_const] using plateauDeriv_near.deriv_eq
  rw [printedL_high _ _ hz, testPoint_im, hD, mul_zero]

theorem lower_raise_plateau_with_constant (x : ℝ) :
    lower (raise (1 / 2) (coordinates plateauAmplitude)) x testHeight +
        (1 / 2 : ℂ) * coordinates plateauAmplitude x testHeight = (9 / 4 : ℂ) := by
  rw [lower, raise_partialX, raise_partialY, coordinates_high _ _ _ testHeight_high,
    plateauAmplitude_near.eq_of_nhds]
  norm_num [testHeight]

theorem raise_lower_plateau (x : ℝ) :
    raise (-3 / 2) (lower (coordinates plateauAmplitude)) x testHeight = (9 / 4 : ℂ) := by
  rw [raise, lower_partialX, lower_partialY, (lower_near x).eq_of_nhds]
  norm_num [testHeight] <;> ring

/-- Both identities in the printed (1.17) already fail at the same point. -/
theorem both_factorizations_fail :
    let F := coordinates plateauAmplitude
    printedL F testPoint ≠
      lower (raise (1 / 2) F) testPoint.re testPoint.im + (1 / 2 : ℂ) * F testPoint.re testPoint.im ∧
    printedL F testPoint ≠ raise (-3 / 2) (lower F) testPoint.re testPoint.im := by
  dsimp only
  rw [printedL_plateau, testPoint_im, lower_raise_plateau_with_constant, raise_lower_plateau]
  norm_num

end
end ManuscriptAudit.Paper9PrintedFactorizations

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9PrintedFactorizations.raise_high,
      ``ManuscriptAudit.Paper9PrintedFactorizations.lower_high,
      ``ManuscriptAudit.Paper9PrintedFactorizations.plateauAmplitude_smooth,
      ``ManuscriptAudit.Paper9PrintedFactorizations.printedL_plateau,
      ``ManuscriptAudit.Paper9PrintedFactorizations.lower_raise_plateau_with_constant,
      ``ManuscriptAudit.Paper9PrintedFactorizations.raise_lower_plateau,
      ``ManuscriptAudit.Paper9PrintedFactorizations.both_factorizations_fail] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
