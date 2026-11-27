import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.BigOperators
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetMass

/-!
# Finite cusp-strip mass from the global modular coset domain

The physical strip of integral width and height at least one is
covered by the corresponding finite list of translates of the
closed modular domain. For any nonnegative invariant density, finite
global mass then implies finite mass in every translated strip.
-/

namespace ManuscriptAudit.Paper8MaassStripCover

open Set MeasureTheory UpperHalfPlane
open FiniteIndexWeightZeroCosets Paper8EtaCosetMass
open Paper8EtaPeterssonMass (translate)
open scoped MatrixGroups ENNReal

noncomputable section

def highStrip (w : ℝ) : Set ℍ :=
  {z | 0 ≤ z.re ∧ z.re ≤ w ∧ 1 ≤ z.im}

theorem highStrip_subset_translates (w : ℕ) :
    highStrip (w : ℝ) ⊆ ⋃ j : Fin (w + 1),
      translate (ModularGroup.T ^ (j.val : ℤ)) ModularGroup.fd := by
  intro z hz
  change 0 ≤ z.re ∧ z.re ≤ (w : ℝ) ∧ 1 ≤ z.im at hz
  let j : ℤ := ⌊z.re + 1 / 2⌋
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (by linarith [hz.1])
  have hJle : (j : ℝ) ≤ z.re + 1 / 2 := Int.floor_le _
  have hJgt : z.re + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hJlt : (j : ℝ) < (w : ℝ) + 1 := by linarith [hz.2.1]
  have hJw : j < (w : ℤ) + 1 := by exact_mod_cast hJlt
  have hCast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  have hW : j.toNat < w + 1 := by
    have hNat : (j.toNat : ℤ) < (w : ℤ) + 1 := by
      rw [hCast]
      exact hJw
    exact_mod_cast hNat
  let k : Fin (w + 1) := ⟨j.toNat, hW⟩
  let u : ℍ := ModularGroup.T ^ (-j) • z
  have hU : (u : ℂ) = (z : ℂ) - (j : ℂ) := by
    unfold u
    rw [UpperHalfPlane.modular_T_zpow_smul]
    simp [UpperHalfPlane.coe_vadd, sub_eq_add_neg, add_comm]
  have hRe : u.re = z.re - (j : ℝ) := by
    change ((u : ℂ).re) = _
    rw [hU]
    simp
  have hIm : u.im = z.im := by
    change ((u : ℂ).im) = _
    rw [hU]
    simp
  have hUfd : u ∈ ModularGroup.fd := by
    change 1 ≤ Complex.normSq (u : ℂ) ∧ |u.re| ≤ (1 : ℝ) / 2
    constructor
    · rw [Complex.normSq_apply]
      change 1 ≤ u.re * u.re + u.im * u.im
      rw [hIm]
      have hY : 1 ≤ z.im * z.im := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hz.2.2) (by linarith [hz.2.2] : 0 ≤ z.im + 1)]
      nlinarith [sq_nonneg u.re]
    · rw [abs_le, hRe]
      constructor <;> linarith
  refine mem_iUnion.mpr ⟨k, u, hUfd, ?_⟩
  change ModularGroup.T ^ (j.toNat : ℤ) • (ModularGroup.T ^ (-j) • z) = z
  rw [hCast, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]

private theorem lintegral_translate_invariant (H : Subgroup SL(2, ℤ)) (density : ℍ → ℝ≥0∞)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, density (h • z) = density z)
    (h : SL(2, ℤ)) (hh : h ∈ H) (S : Set ℍ) :
    (∫⁻ z in translate h S, density z) = ∫⁻ z in S, density z := by
  have hMeasure : MeasurePreserving (fun z : ℍ => h • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (h : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => h • z) :=
    measurableEmbedding_const_smul (h : GL (Fin 2) ℝ)
  simpa only [translate, hInv h hh] using (hMeasure.setLIntegral_comp_emb hEmb density S).symm

theorem translate_fd_mass_lt_top (H : Subgroup SL(2, ℤ)) (density : ℍ → ℝ≥0∞)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, density (h • z) = density z)
    (hMass : (∫⁻ z in cosetCells H ModularGroup.fd, density z) < ⊤)
    (g : SL(2, ℤ)) :
    (∫⁻ z in translate g ModularGroup.fd, density z) < ⊤ := by
  let q := rightCosetMk H g
  let a := cellRepresentative H q
  have haq : rightCosetMk H g = rightCosetMk H a := (cellRepresentative_mk H q).symm
  let h := g * a⁻¹
  have hh : h ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact haq.symm)
  have hga : g = h * a := by simp [h, mul_assoc]
  have hSets : translate g ModularGroup.fd = translate h (translate a ModularGroup.fd) := by
    rw [hga]
    simp only [translate, image_image, mul_smul]
  have hSub : translate a ModularGroup.fd ⊆ cosetCells H ModularGroup.fd := by
    intro x hx
    exact mem_iUnion.mpr ⟨q, hx⟩
  rw [hSets, lintegral_translate_invariant H density hInv h hh]
  exact (lintegral_mono_set hSub).trans_lt hMass

theorem cusp_mass_lt_top (H : Subgroup SL(2, ℤ)) (density : ℍ → ℝ≥0∞)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, density (h • z) = density z)
    (hMass : (∫⁻ z in cosetCells H ModularGroup.fd, density z) < ⊤)
    (g : SL(2, ℤ)) (w : ℕ) :
    (∫⁻ z in highStrip (w : ℝ), density (g • z)) < ⊤ := by
  let U (j : Fin (w + 1)) := translate (g * ModularGroup.T ^ (j.val : ℤ)) ModularGroup.fd
  have hSub : translate g (highStrip (w : ℝ)) ⊆ ⋃ j, U j := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.mp (highStrip_subset_translates w hz)
    exact mem_iUnion.mpr ⟨j, u, hu, mul_smul _ _ _⟩
  have hMeasure : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  have hPull : (∫⁻ z in highStrip (w : ℝ), density (g • z)) =
      ∫⁻ z in translate g (highStrip (w : ℝ)), density z :=
    hMeasure.setLIntegral_comp_emb hEmb density _
  rw [hPull]
  refine (lintegral_mono_set hSub).trans_lt ((lintegral_iUnion_le U density).trans_lt ?_)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun j _ => translate_fd_mass_lt_top H density hInv hMass _)

end
end ManuscriptAudit.Paper8MaassStripCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassStripCover.highStrip_subset_translates,
      ``ManuscriptAudit.Paper8MaassStripCover.translate_fd_mass_lt_top,
      ``ManuscriptAudit.Paper8MaassStripCover.cusp_mass_lt_top] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
