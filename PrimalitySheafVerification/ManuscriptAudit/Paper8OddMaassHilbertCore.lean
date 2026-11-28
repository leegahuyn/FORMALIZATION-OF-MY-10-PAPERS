import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.L2Space
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCutoffEnergy

/-! The actual odd multiplier's smooth cusp-compact core and intrinsic L² realization. -/

namespace ManuscriptAudit.Paper8OddMaassHilbertCore

open Filter Set MeasureTheory UpperHalfPlane
open Paper8EtaCriticalOddVanishing Paper8OddGlobalCutoffEnergy Paper8OddCrossCuspRows
open Paper8EtaHalfWeightPhase Paper8CompactCurrentGreen Paper8ModularHeightCutoff
open scoped MatrixGroups ENNReal ContDiff InnerProductSpace

noncomputable section

def oddMaassMeasure : Measure ℍ := volume.restrict levelFourCells

abbrev OddMaassL2 := Lp ℂ 2 oddMaassMeasure

def OddSmoothCompactCore : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | OddMaassLaw F ∧ ContDiffOn ℝ ∞ F {w : ℂ | 0 < w.im} ∧
    ∃ B : ℝ, ∀ z : ℍ, B < maximumHeight z → F z = 0}
  zero_mem' := by
    refine ⟨?_, ?_, ⟨0, fun _ _ => rfl⟩⟩
    · intro g z
      simp
    · exact contDiffOn_const
  add_mem' := by
    intro F G hF hG
    obtain ⟨hLF, hSF, BF, hCF⟩ := hF
    obtain ⟨hLG, hSG, BG, hCG⟩ := hG
    refine ⟨?_, hSF.add hSG, ⟨max BF BG, ?_⟩⟩
    · intro g z
      change F ((g : SL(2, ℤ)) • z : ℍ) + G ((g : SL(2, ℤ)) • z : ℍ) =
        (levelCharacter g : ℂ) * negativePhase (g : SL(2, ℤ)) z * (F z + G z)
      rw [hLF, hLG, mul_add]
    · intro z hz
      change F z + G z = 0
      rw [hCF z ((le_max_left _ _).trans_lt hz), hCG z ((le_max_right _ _).trans_lt hz), add_zero]
  smul_mem' := by
    intro c F hF
    obtain ⟨hLF, hSF, BF, hCF⟩ := hF
    refine ⟨?_, hSF.const_smul c, ⟨BF, ?_⟩⟩
    · intro g z
      change c * F ((g : SL(2, ℤ)) • z : ℍ) =
        (levelCharacter g : ℂ) * negativePhase (g : SL(2, ℤ)) z * (c * F z)
      rw [hLF]
      ring
    · intro z hz
      change c * F z = 0
      rw [hCF z hz, mul_zero]

theorem oddCore_continuous (f : OddSmoothCompactCore) :
    Continuous (fun z : ℍ => (f : ℂ → ℂ) z) :=
  f.2.2.1.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

theorem oddCore_memLp (f : OddSmoothCompactCore) :
    MemLp (fun z : ℍ => (f : ℂ → ℂ) z) 2 oddMaassMeasure := by
  obtain ⟨B, hB⟩ := f.2.2.2
  apply (memLp_two_iff_integrable_sq_norm (oddCore_continuous f).measurable.aestronglyMeasurable).2
  change IntegrableOn (fun z : ℍ => ‖(f : ℂ → ℂ) z‖ ^ 2) levelFourCells
  exact integrableOn_cusp_support (CongruenceSubgroup.Gamma0 4) _
    ((oddCore_continuous f).norm.pow 2) (B := B) (fun z hz => by rw [hB z hz, norm_zero] <;> norm_num)

def oddCoreVector (f : OddSmoothCompactCore) : OddMaassL2 :=
  (oddCore_memLp f).toLp (fun z : ℍ => (f : ℂ → ℂ) z)

def oddCoreLinear : OddSmoothCompactCore →ₗ[ℂ] OddMaassL2 where
  toFun := oddCoreVector
  map_add' := by
    intro f g
    exact MemLp.toLp_add (oddCore_memLp f) (oddCore_memLp g)
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (oddCore_memLp (c • f)), MemLp.coeFn_toLp (oddCore_memLp f),
      Lp.coeFn_smul c (oddCoreVector f)] with z h₁ h₂ h₃
    change oddCoreVector (c • f) z = (((c • f : OddSmoothCompactCore) : ℂ → ℂ) z) at h₁
    change oddCoreVector f z = (f : ℂ → ℂ) z at h₂
    change (c • oddCoreVector f) z = c • oddCoreVector f z at h₃
    change oddCoreVector (c • f) z = (c • oddCoreVector f) z
    rw [h₁, h₃, h₂] <;> rfl

def oddMaassHilbertSubmodule : Submodule ℂ OddMaassL2 :=
  oddCoreLinear.range.topologicalClosure

abbrev OddMaassHilbertSpace := oddMaassHilbertSubmodule

instance : CompleteSpace OddMaassHilbertSpace := by
  have hClosed : IsClosed (oddMaassHilbertSubmodule : Set OddMaassL2) := isClosed_closure
  exact hClosed.completeSpace_coe

theorem oddCoreVector_inner (f g : OddSmoothCompactCore) :
    ⟪oddCoreVector f, oddCoreVector g⟫_ℂ =
      ∫ z in levelFourCells, ⟪(f : ℂ → ℂ) z, (g : ℂ → ℂ) z⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  change (∫ z, ⟪oddCoreVector f z, oddCoreVector g z⟫_ℂ ∂oddMaassMeasure) = _
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (oddCore_memLp f), MemLp.coeFn_toLp (oddCore_memLp g)] with z hf hg
  change oddCoreVector f z = (f : ℂ → ℂ) z at hf
  change oddCoreVector g z = (g : ℂ → ℂ) z at hg
  change ⟪oddCoreVector f z, oddCoreVector g z⟫_ℂ = _
  rw [hf, hg]

end
end ManuscriptAudit.Paper8OddMaassHilbertCore

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddMaassHilbertCore.oddCoreLinear,
      ``ManuscriptAudit.Paper8OddMaassHilbertCore.oddCoreVector_inner] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
