import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Simple-root lifting on the actual p-adic integer ring

The residue morphism converts congruence conditions to norm conditions
in Mathlib's Hensel theorem. On the good locus, where residue roots
are simple, the resulting lift is unique with the specified residue.
-/

namespace ManuscriptAudit.PadicHenselGate

open Polynomial

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private abbrev reduction : ℤ_[p] →+* ZMod p := PadicInt.toZMod

theorem norm_lt_one_iff_reduction_zero (a : ℤ_[p]) :
    ‖a‖ < 1 ↔ reduction a = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

private theorem norm_sub_lt_one_iff (x y : ℤ_[p]) :
    ‖x - y‖ < 1 ↔ reduction x = reduction y := by
  rw [norm_lt_one_iff_reduction_zero, map_sub, sub_eq_zero]

/-- An actual simple residue root has a unique p-adic lift in its residue class. -/
theorem unique_lift_from_simple {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
    (F : Polynomial R) (a : ℤ_[p]) (hRoot : reduction (F.aeval a) = 0)
    (hSimple : reduction (F.derivative.aeval a) ≠ 0) :
    ∃! z : ℤ_[p], F.aeval z = 0 ∧ reduction z = reduction a := by
  have hNormDerivative : ‖F.derivative.aeval a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt ?_)
    intro hn
    exact hSimple ((norm_lt_one_iff_reduction_zero _).mp hn)
  have hNorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hNormDerivative, one_pow]
    exact (norm_lt_one_iff_reduction_zero _).mpr hRoot
  obtain ⟨z, hz, hClose, hDerivative, hUnique⟩ := hensels_lemma hNorm
  have hClose' : ‖z - a‖ < 1 := hNormDerivative ▸ hClose
  refine ⟨z, ⟨hz, (norm_sub_lt_one_iff z a).mp hClose'⟩, ?_⟩
  intro w hw
  apply hUnique w hw.1
  rw [hNormDerivative]
  exact (norm_sub_lt_one_iff w a).mpr hw.2

/-- The simple-root statement with the residue polynomial and its derivative. -/
theorem residue_simple_root_unique_lift (F : Polynomial (ℤ_[p])) (r : ZMod p)
    (hRoot : (F.map reduction).eval r = 0)
    (hDerivative : (derivative (F.map reduction)).eval r ≠ 0) :
    ∃! z : ℤ_[p], F.eval z = 0 ∧ reduction z = r := by
  obtain ⟨a, ha⟩ := (ZMod.ringHom_surjective (reduction : ℤ_[p] →+* ZMod p)) r
  rw [← ha] at *
  have hRoot' : reduction (F.eval a) = 0 := by
    simpa only [Polynomial.eval_map_apply] using hRoot
  have hDerivative' : reduction (F.derivative.eval a) ≠ 0 := by
    simpa only [Polynomial.derivative_map, Polynomial.eval_map_apply] using hDerivative
  exact unique_lift_from_simple F a hRoot' hDerivative'

/-- The good-locus equivalence for a specified polynomial and residue. -/
theorem good_residue_root_iff_unique_lift (F : Polynomial (ℤ_[p])) (r : ZMod p)
    (hGood : (F.map reduction).eval r = 0 →
      (derivative (F.map reduction)).eval r ≠ 0) :
    ((F.map reduction).eval r = 0 ∧ (derivative (F.map reduction)).eval r ≠ 0) ↔
      ∃! z : ℤ_[p], F.eval z = 0 ∧ reduction z = r := by
  constructor
  · exact fun h => residue_simple_root_unique_lift F r h.1 h.2
  · rintro ⟨z, ⟨hRoot, hResidue⟩, hUnique⟩
    have h : (F.map reduction).eval r = 0 := by
      rw [← hResidue, Polynomial.eval_map_apply, hRoot, map_zero]
    exact ⟨h, hGood h⟩

/-- Nonvanishing of the actual residual resultant certifies simplicity
at every residue root. -/
theorem resultant_good_residue_lift (F : Polynomial (ℤ_[p])) (r : ZMod p)
    (hNonzero : F.map reduction ≠ 0)
    (hResultant : resultant (F.map reduction) (derivative (F.map reduction)) ≠ 0) :
    ((F.map reduction).eval r = 0) ↔
      ∃! z : ℤ_[p], F.eval z = 0 ∧ reduction z = r := by
  have hCoprime : IsCoprime (F.map reduction) (derivative (F.map reduction)) := by
    by_contra h
    exact hResultant (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hNonzero, h⟩)
  have hSimple : (F.map reduction).eval r = 0 →
      (derivative (F.map reduction)).eval r ≠ 0 := by
    intro hRoot hBad
    obtain ⟨A, B, hAB⟩ := hCoprime
    have h := congrArg (Polynomial.eval r) hAB
    simp [hRoot, hBad] at h
  exact ⟨fun h => residue_simple_root_unique_lift F r h (hSimple h),
    fun h => ((good_residue_root_iff_unique_lift F r hSimple).mpr h).1⟩

/-- A repeated root can have a unique p-adic lift in the absence of the good-locus condition. -/
theorem repeated_root_unique_lift :
    (derivative ((X : Polynomial (ZMod p)) ^ 2)).eval 0 = 0 ∧
      ∃! z : ℤ_[p], ((X : Polynomial (ℤ_[p])) ^ 2).eval z = 0 ∧ reduction z = 0 := by
  refine ⟨by simp [pow_two], 0, by simp, ?_⟩
  intro z hz
  have h : z ^ 2 = 0 := by simpa using hz.1
  exact pow_eq_zero h

end

end ManuscriptAudit.PadicHenselGate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicHenselGate.norm_lt_one_iff_reduction_zero,
      ``ManuscriptAudit.PadicHenselGate.unique_lift_from_simple,
      ``ManuscriptAudit.PadicHenselGate.residue_simple_root_unique_lift,
      ``ManuscriptAudit.PadicHenselGate.good_residue_root_iff_unique_lift,
      ``ManuscriptAudit.PadicHenselGate.resultant_good_residue_lift,
      ``ManuscriptAudit.PadicHenselGate.repeated_root_unique_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
