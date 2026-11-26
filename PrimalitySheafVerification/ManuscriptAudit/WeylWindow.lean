import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative transfer of a Weyl remainder to spectral windows

Paper 10, physical PDF p. 500, Proposition 4.27 and Corollary 4.28.
A discrete reference sequence is counted with multiplicity by its index set.
A quantitative Weyl remainder for that sequence and a uniform bound on
the matched eigenvalue drift give an explicit O(T) count on a closed unit
window in the nonnegative real spectral parameter.
-/

namespace ManuscriptAudit.WeylWindow

noncomputable section

def energy (t : ℝ) : ℝ := 1 / 4 + t ^ 2

def levelsBelow {I : Type*} (reference : I → ℝ) (e : ℝ) : Set I :=
  {i | reference i ≤ e}

def levelCount {I : Type*} (reference : I → ℝ) (e : ℝ) : ℝ :=
  (levelsBelow reference e).ncard

def closedWindow {I : Type*} (t : I → ℝ) (T : ℝ) : Set I :=
  {i | T ≤ t i ∧ t i ≤ T + 1}

def lowerCutoff (T B : ℝ) : ℝ := energy (T - 1) - B

def upperCutoff (T B : ℝ) : ℝ := energy (T + 1) + B

private theorem energy_order_on_window {u T : ℝ} (hT : 1 ≤ T)
    (h₁ : T ≤ u) (h₂ : u ≤ T + 1) :
    energy T ≤ energy u ∧ energy u ≤ energy (T + 1) := by
  unfold energy
  have hleft : 0 ≤ u + T := by linarith only [h₁, hT]
  have hright : 0 ≤ T + 1 + u := by linarith only [h₁, hT]
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) hleft]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h₂) hright]

private theorem window_subset_reference_cutoffs
    {I : Type*} (reference perturbed t : I → ℝ) {T B : ℝ} (hT : 1 ≤ T)
    (hparam : ∀ i, perturbed i = energy (t i))
    (hdrift : ∀ i, |perturbed i - reference i| ≤ B) :
    closedWindow t T ⊆
      levelsBelow reference (upperCutoff T B) \ levelsBelow reference (lowerCutoff T B) := by
  have hstep : energy (T - 1) < energy T := by
    unfold energy
    nlinarith only [hT]
  intro i hi
  have hi' : T ≤ t i ∧ t i ≤ T + 1 := hi
  have hlevel := energy_order_on_window hT hi'.1 hi'.2
  rw [← hparam i] at hlevel
  have hd := abs_le.mp (hdrift i)
  constructor
  · change reference i ≤ energy (T + 1) + B
    linarith only [hlevel.2, hd.1]
  · intro hlow
    change reference i ≤ energy (T - 1) - B at hlow
    linarith only [hlevel.1, hd.2, hlow, hstep]

/-- The lower reference cutoff is strictly below every relevant reference level.
This handles the included left endpoint of the spectral window. -/
theorem window_count_le_cutoff_difference
    {I : Type*} (reference perturbed t : I → ℝ) {T B : ℝ}
    (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hparam : ∀ i, perturbed i = energy (t i))
    (hdrift : ∀ i, |perturbed i - reference i| ≤ B)
    (hfinite : (levelsBelow reference (upperCutoff T B)).Finite) :
    ((closedWindow t T).ncard : ℝ) ≤
      levelCount reference (upperCutoff T B) - levelCount reference (lowerCutoff T B) := by
  have hsubset :
      levelsBelow reference (lowerCutoff T B) ⊆ levelsBelow reference (upperCutoff T B) := by
    intro i hi
    change reference i ≤ upperCutoff T B
    change reference i ≤ lowerCutoff T B at hi
    refine hi.trans ?_
    unfold lowerCutoff upperCutoff energy
    nlinarith only [hT, hB]
  have hcard := Set.ncard_le_ncard
    (window_subset_reference_cutoffs reference perturbed t hT hparam hdrift)
    (hfinite.subset Set.sdiff_subset)
  have hcast :
      ((closedWindow t T).ncard : ℝ) ≤
        ((levelsBelow reference (upperCutoff T B) \
          levelsBelow reference (lowerCutoff T B)).ncard : ℝ) := by
    exact_mod_cast hcard
  rw [Set.cast_ncard_sdiff hsubset hfinite] at hcast
  exact hcast

private theorem sqrt_abs_cutoff_le {u B e : ℝ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (he : |e| ≤ u ^ 2 + (1 / 4 + B)) :
    Real.sqrt |e| ≤ u + Real.sqrt (1 / 4 + B) := by
  have hK : 0 ≤ (1 / 4 : ℝ) + B := by linarith only [hB]
  have hS := Real.sqrt_nonneg ((1 / 4 : ℝ) + B)
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg hu hS, ?_⟩
  nlinarith only [he, Real.sq_sqrt hK, mul_nonneg hu hS]

/-- Explicit linear bound from a quantitative reference counting remainder.
The drift assumption is about matched eigenvalues counted with multiplicity. -/
theorem window_count_le_of_weyl_remainder
    {I : Type*} (reference perturbed t : I → ℝ) {a D B T : ℝ}
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hparam : ∀ i, perturbed i = energy (t i))
    (hdrift : ∀ i, |perturbed i - reference i| ≤ B)
    (hfinite : ∀ e, (levelsBelow reference e).Finite)
    (hremainder : ∀ e, 0 ≤ e →
      |levelCount reference e - a * e| ≤ D * (1 + Real.sqrt |e|)) :
    ((closedWindow t T).ncard : ℝ) ≤
      (a * (4 + 2 * B) + D * (2 + 2 * Real.sqrt (1 / 4 + B))) * (1 + T) := by
  let lo := lowerCutoff T B
  let hi := upperCutoff T B
  let S := Real.sqrt (1 / 4 + B)
  have hT₀ : 0 ≤ T := by linarith only [hT]
  have hi₀ : 0 ≤ hi := by
    dsimp [hi, upperCutoff, energy]
    nlinarith only [hB, sq_nonneg (T + 1)]
  have hhi : levelCount reference hi - a * hi ≤ D * (1 + Real.sqrt |hi|) :=
    (abs_le.mp (hremainder hi hi₀)).2
  have hlo : -(D * (1 + Real.sqrt |lo|)) ≤ levelCount reference lo - a * lo := by
    by_cases hlo₀ : 0 ≤ lo
    · exact (abs_le.mp (hremainder lo hlo₀)).1
    · have hc : 0 ≤ levelCount reference lo := Nat.cast_nonneg _
      have hat : a * lo ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hlo₀)
      have hdt : 0 ≤ D * (1 + Real.sqrt |lo|) :=
        mul_nonneg hD (add_nonneg zero_le_one (Real.sqrt_nonneg _))
      linarith only [hc, hat, hdt]
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hshi : Real.sqrt |hi| ≤ T + 1 + S := by
    apply sqrt_abs_cutoff_le (show 0 ≤ T + 1 by linarith only [hT]) hB
    rw [abs_of_nonneg hi₀]
    dsimp [hi, upperCutoff, energy]
    linarith
  have hslo : Real.sqrt |lo| ≤ T - 1 + S := by
    apply sqrt_abs_cutoff_le (sub_nonneg.mpr hT) hB
    dsimp [lo, lowerCutoff, energy]
    apply abs_le.mpr
    constructor <;> nlinarith only [hB, sq_nonneg (T - 1)]
  have hw : hi - lo = 4 * T + 2 * B := by
    dsimp [hi, lo, upperCutoff, lowerCutoff, energy]
    ring
  have hmain : 4 * T + 2 * B ≤ (4 + 2 * B) * (1 + T) := by
    nlinarith only [mul_nonneg hB hT₀]
  have herrors : 2 + Real.sqrt |hi| + Real.sqrt |lo| ≤ (2 + 2 * S) * (1 + T) := by
    nlinarith only [hshi, hslo, mul_nonneg hS hT₀]
  calc
    ((closedWindow t T).ncard : ℝ) ≤ levelCount reference hi - levelCount reference lo :=
      window_count_le_cutoff_difference reference perturbed t hT hB hparam hdrift (hfinite hi)
    _ ≤ a * (hi - lo) + D * (2 + Real.sqrt |hi| + Real.sqrt |lo|) := by
      nlinarith only [hhi, hlo]
    _ ≤ a * ((4 + 2 * B) * (1 + T)) + D * ((2 + 2 * S) * (1 + T)) := by
      rw [hw]
      exact add_le_add (mul_le_mul_of_nonneg_left hmain ha)
        (mul_le_mul_of_nonneg_left herrors hD)
    _ = (a * (4 + 2 * B) + D * (2 + 2 * S)) * (1 + T) := by ring

end

end ManuscriptAudit.WeylWindow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeylWindow.window_count_le_cutoff_difference,
      ``ManuscriptAudit.WeylWindow.window_count_le_of_weyl_remainder] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
