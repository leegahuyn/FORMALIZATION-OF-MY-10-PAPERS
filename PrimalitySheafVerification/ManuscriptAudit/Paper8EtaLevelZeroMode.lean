import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindZeroReference
import PrimalitySheafVerification.ManuscriptAudit.Paper8NormalizedKloostermanRows

/-!
# Exact level restriction of the eta-multiplier sum at zero Fourier mode

The finite Kloosterman sum uses Ahlgren–Andersen, arXiv:1504.02500v3,
§6 and (7.1), at m = n = 1. Its multiplier phase is specified for
positive lower left entry, and the cusp width at infinity is one for
every Γ₀(N). The universal factor is exp(2πi/8).
-/

namespace ManuscriptAudit.Paper8EtaLevelZeroMode

open Matrix
open Paper8NormalizedKloostermanRows
open Paper8ContourResidueWeights (dedekindSum)
open Paper8DedekindZeroReference (referenceZeroSum)
open Paper8HolomorphicPartPhase (periodCoefficient)

noncomputable section

def etaPhase : ℂ :=
  Complex.exp (periodCoefficient * ((1 / 8 : ℝ) : ℂ))

def diagonalPhase {D : ℕ} (A : NormalizedRow D) : ℝ :=
  ((A.1 0 0 : ℝ) + (A.1 1 1 : ℝ)) / (24 * (D : ℝ))

def etaMultiplier {D : ℕ} (A : NormalizedRow D) : ℂ :=
  Complex.exp (periodCoefficient *
    ((diagonalPhase A - (dedekindSum (A.1 1 1) D : ℝ) / 2 - 1 / 8 : ℝ) : ℂ))

def zeroModeEntry {D : ℕ} (A : NormalizedRow D) : ℂ :=
  (starRingEnd ℂ) (etaMultiplier A) *
    Complex.exp (periodCoefficient * (diagonalPhase A : ℂ))

def referenceEntry (D : ℕ) (d : ℤ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum d D : ℝ) : ℂ))

theorem translation_mem_level (N : ℕ) :
    ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  change (((ModularGroup.T.1 1 0 : ℤ) : ZMod N) = 0)
  rw [ModularGroup.coe_T]
  simp

theorem zeroModeEntry_eq {D : ℕ} (A : NormalizedRow D) :
    zeroModeEntry A = etaPhase * referenceEntry D (A.1 1 1) := by
  unfold zeroModeEntry etaMultiplier etaPhase referenceEntry
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [periodCoefficient, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

@[instance_reducible] private noncomputable def normalizedFintype {D : ℕ} (hD : 0 < D) :
    Fintype (NormalizedRow D) :=
  Fintype.ofEquiv (ReducedResidue D) (rowsEquiv hD).symm

/-- The sum at m = n = 1 over the normalized rows belonging to Γ₀(N). -/
def levelSum (N : ℕ) {D : ℕ} (hD : 0 < D) : ℂ := by
  classical
  letI := normalizedFintype hD
  exact ∑ A : NormalizedRow D,
    if A.1 ∈ CongruenceSubgroup.Gamma0 N then zeroModeEntry A else 0

private theorem referenceZeroSum_subtype (D : ℕ) :
    referenceZeroSum D =
      ∑ d : ReducedResidue D, referenceEntry D (d.1.val : ℤ) := by
  unfold referenceZeroSum
  exact Finset.sum_subtype _ (fun d => by simp) _

theorem levelSum_eq (N : ℕ) {D : ℕ} (hD : 0 < D) :
    levelSum N hD = if N ∣ D then etaPhase * referenceZeroSum D else 0 := by
  classical
  letI := normalizedFintype hD
  unfold levelSum
  by_cases hN : N ∣ D
  · rw [if_pos hN]
    calc
      _ = ∑ A : NormalizedRow D,
          etaPhase * referenceEntry D (A.1 1 1) := by
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [if_pos ((row_mem_level_iff N A).mpr hN), zeroModeEntry_eq]
      _ = ∑ d : ReducedResidue D, etaPhase * referenceEntry D (d.1.val : ℤ) := by
        refine Fintype.sum_equiv (rowsEquiv hD) _ _ (fun A => ?_)
        rw [rowsEquiv_bottom_cast hD A]
      _ = etaPhase * referenceZeroSum D := by
        rw [referenceZeroSum_subtype, Finset.mul_sum]
  · rw [if_neg hN]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    exact if_neg (fun hA => hN ((row_mem_level_iff N A).1 hA))

theorem levelFour_eq_progression_zero {D : ℕ} (hD : 0 < D) :
    levelSum 4 hD = if D % 4 = 0 then etaPhase * referenceZeroSum D else 0 := by
  rw [levelSum_eq]
  by_cases h : D % 4 = 0
  · rw [if_pos h, if_pos (Nat.dvd_iff_mod_eq_zero.mpr h)]
  · rw [if_neg h, if_neg (fun hd => h (Nat.dvd_iff_mod_eq_zero.mp hd))]

theorem levelTwo_sub_levelFour_eq_progression_two {D : ℕ} (hD : 0 < D) :
    levelSum 2 hD - levelSum 4 hD =
      if D % 4 = 2 then etaPhase * referenceZeroSum D else 0 := by
  rw [levelSum_eq, levelFour_eq_progression_zero]
  by_cases h0 : D % 4 = 0
  · have hEven : 2 ∣ D := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    simp [h0, hEven]
  · by_cases h2 : D % 4 = 2
    · have hEven : 2 ∣ D := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      simp [h0, h2, hEven]
    · have hOdd : ¬ 2 ∣ D := by
        intro hDvd
        have := Nat.dvd_iff_mod_eq_zero.mp hDvd
        omega
      simp [h0, h2, hOdd]

end
end ManuscriptAudit.Paper8EtaLevelZeroMode

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaLevelZeroMode.translation_mem_level,
      ``ManuscriptAudit.Paper8EtaLevelZeroMode.zeroModeEntry_eq,
      ``ManuscriptAudit.Paper8EtaLevelZeroMode.levelSum_eq,
      ``ManuscriptAudit.Paper8EtaLevelZeroMode.levelFour_eq_progression_zero,
      ``ManuscriptAudit.Paper8EtaLevelZeroMode.levelTwo_sub_levelFour_eq_progression_two] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
