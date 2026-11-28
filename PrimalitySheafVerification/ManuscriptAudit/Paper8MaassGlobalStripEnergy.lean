import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassStripFubini
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCriticalOddVanishing

/-! Global coset L² mass suffices in the actual odd Maass raising-kernel theorem. -/

namespace ManuscriptAudit.Paper8MaassGlobalStripEnergy

open Set MeasureTheory UpperHalfPlane
open Paper8EtaCriticalOddVanishing
open Paper8EtaCosetMass (cosetCells)
open scoped MatrixGroups ENNReal

noncomputable section

abbrev normSquareDensity := Paper8MaassStripFubini.normSquareDensity

theorem maassStripEnergy_integrable_of_global_mass {H : Subgroup SL(2, ℤ)} {F : ℂ → ℂ}
    (hF : Measurable (fun z : ℍ => F z))
    (hInv : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, ‖F (h • z : ℍ)‖ = ‖F z‖)
    (hMass : (∫⁻ z in cosetCells H ModularGroup.fd, normSquareDensity F z) < ⊤)
    (g : SL(2, ℤ)) (w : ℕ) :
    IntegrableOn (maassStripEnergy F g (w : ℝ)) (Ioi 1) :=
  Paper8MaassStripFubini.stripEnergy_integrable_of_global_mass hF hInv hMass g w

theorem odd_maass_raising_kernel_eq_zero_of_global_mass {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ F z)
    (hKernel : ∀ x y : ℝ, 0 < y →
      Paper8NegativeHalfMaassFactorization.raising (Paper8MaassCriticalHolomorphic.realProfile F) x y = 0)
    (hMass : (∫⁻ z in cosetCells (CongruenceSubgroup.Gamma0 4) ModularGroup.fd, normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, F z = 0 := by
  have hCont : Continuous (fun z : ℍ => F z) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    exact (hF z z.im_pos).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
  have hInv (h : SL(2, ℤ)) (hh : h ∈ CongruenceSubgroup.Gamma0 4) (z : ℍ) :
      ‖F (h • z : ℍ)‖ = ‖F z‖ := by
    have hChar := congrArg (fun a : ℂ => ‖a‖)
      (Paper8EtaInverseWeightedVanishing.levelCharacter_sq (⟨h, hh⟩ : CongruenceSubgroup.Gamma0 4))
    rw [norm_pow, norm_one] at hChar
    have hCharNorm := (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (2 : ℕ) ≠ 0)).mp
      (hChar.trans (one_pow _).symm)
    rw [hLaw ⟨h, hh⟩ z, norm_mul, norm_mul, hCharNorm, Paper8EtaHalfWeightPhase.negativePhase_norm,
      one_mul, one_mul]
  exact odd_maass_raising_kernel_eq_zero hLaw hF hKernel (fun g =>
    maassStripEnergy_integrable_of_global_mass hCont.measurable hInv hMass g 4)

end
end ManuscriptAudit.Paper8MaassGlobalStripEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassGlobalStripEnergy.maassStripEnergy_integrable_of_global_mass,
      ``ManuscriptAudit.Paper8MaassGlobalStripEnergy.odd_maass_raising_kernel_eq_zero_of_global_mass] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
