import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9GammaTwoSign

/-! A unitary twist with no phase-one cusp at any of the three actual cusps. -/

namespace ManuscriptAudit.Paper9GammaTwoNoChannels

open Matrix Matrix.SpecialLinearGroup
open LiteralCuspTruncation (GammaTwo)
open CompactModularCore (reduceTwo mem_gamma_iff_reduced_one)
open ModularGroup (S)
open Paper9GammaTwoSign
open scoped MatrixGroups

noncomputable section

/-- Conjugation by the cusp scaling matrix S normalizes the literal Γ(2). -/
def conjugateByS : GammaTwo →* GammaTwo where
  toFun g :=
    ⟨S * (g : SL(2, ℤ)) * S⁻¹, by
      apply (mem_gamma_iff_reduced_one _).mpr
      have hg := (mem_gamma_iff_reduced_one _).mp g.property
      simp [hg]⟩
  map_one' := by
    apply Subtype.ext
    change S * (1 : SL(2, ℤ)) * S⁻¹ = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    change S * ((g : SL(2, ℤ)) * (h : SL(2, ℤ))) * S⁻¹ =
      (S * (g : SL(2, ℤ)) * S⁻¹) * (S * (h : SL(2, ℤ)) * S⁻¹)
    simp [mul_assoc]

def lowerLeftSign : GammaTwo →* ℂ := upperRightSign.comp conjugateByS

theorem lowerLeftSign_unitary (g : GammaTwo) : ‖lowerLeftSign g‖ = 1 :=
  upperRightSign_unitary (conjugateByS g)

theorem lowerLeftSign_cuspParabolic (i : Fin 3) :
    lowerLeftSign (cuspParabolic i) = ![(1 : ℂ), -1, -1] i := by
  have h : halfUpperRight (conjugateByS (cuspParabolic i)) = ![(0 : ZMod 2), 1, 1] i := by
    fin_cases i <;> decide
  change (if halfUpperRight (conjugateByS (cuspParabolic i)) = 0 then (1 : ℂ) else -1) = _
  rw [h]
  fin_cases i <;> norm_num

def bothSigns : GammaTwo →* ℂ := upperRightSign * lowerLeftSign

theorem bothSigns_unitary (g : GammaTwo) : ‖bothSigns g‖ = 1 := by
  change ‖upperRightSign g * lowerLeftSign g‖ = 1
  rw [norm_mul, upperRightSign_unitary, lowerLeftSign_unitary, one_mul]

theorem twist_preserves_cocycle {X : Type*} [MulAction GammaTwo X]
    (j : GammaTwo → X → ℂ)
    (hj : ∀ g h x, j (g * h) x = j g (h • x) * j h x)
    (g h : GammaTwo) (x : X) :
    bothSigns (g * h) * j (g * h) x =
      (bothSigns g * j g (h • x)) * (bothSigns h * j h x) := by
  rw [map_mul, hj]
  ring

theorem twisted_phases (i : Fin 3) :
    bothSigns (cuspParabolic i) * Paper9ThetaCuspPhases.parabolicPhase i =
      ![(-1 : ℂ), -1, Complex.I] i := by
  change (upperRightSign (cuspParabolic i) * lowerLeftSign (cuspParabolic i)) *
    Paper9ThetaCuspPhases.parabolicPhase i = _
  rw [upperRightSign_cuspParabolic, lowerLeftSign_cuspParabolic]
  fin_cases i <;> norm_num [Paper9ThetaCuspPhases.parabolicPhase]

theorem no_trivial_phase (i : Fin 3) :
    bothSigns (cuspParabolic i) * Paper9ThetaCuspPhases.parabolicPhase i ≠ 1 := by
  rw [twisted_phases]
  have hi : (Complex.I : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  have hm : (-1 : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  fin_cases i <;> simp [hi, hm]

end
end ManuscriptAudit.Paper9GammaTwoNoChannels

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.lowerLeftSign_unitary,
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.lowerLeftSign_cuspParabolic,
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.bothSigns_unitary,
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.twist_preserves_cocycle,
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.twisted_phases,
      ``ManuscriptAudit.Paper9GammaTwoNoChannels.no_trivial_phase] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
