import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.ExactSupportDetection

/-!
# Reduction changes the exact-support detection index

Paper 6, Proposition 7.2(2) on physical p. 201, asserts invariance
under reduction at every prime. The support consisting of the point
(3) has index zero. Its inverse image under reduction modulo 2 is
empty, where the exact-support index is infinity.
-/

namespace ManuscriptAudit.SpecIntSupportReduction

open CategoryTheory CategoryTheory.Abelian
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ExactSupportDetection

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

local instance (S : TopCat.{0}) : HasExt.{0} (AbelianSheaf S) :=
  IsGrothendieckAbelian.hasExt _

/-- The integer prime point defined by reduction modulo 3. -/
def primeThree : PrimeSpectrum ℤ :=
  PrimeSpectrum.comap (Int.castRingHom (ZMod 3)) ⊥

theorem three_mem_primeThree : (3 : ℤ) ∈ primeThree.asIdeal := by
  change (↑(3 : ℤ) : ZMod 3) ∈ (⊥ : Ideal (ZMod 3))
  exact Ideal.mem_bot.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (by norm_num))

theorem two_not_mem_primeThree : (2 : ℤ) ∉ primeThree.asIdeal := by
  change (↑(2 : ℤ) : ZMod 3) ∉ (⊥ : Ideal (ZMod 3))
  intro h
  have hDvd := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 3).mp (Ideal.mem_bot.mp h)
  norm_num at hDvd

theorem primeThree_ne_generic : primeThree.asIdeal ≠ ⊥ := by
  intro h
  have hThree := three_mem_primeThree
  rw [h] at hThree
  have hZero : (3 : ℤ) = 0 := Ideal.mem_bot.mp hThree
  norm_num at hZero

/-- Each point of the characteristic-two fiber pulls back to an ideal containing 2. -/
theorem two_mem_reduction_comap (x : PrimeSpectrum (ZMod 2)) :
    (2 : ℤ) ∈ (PrimeSpectrum.comap (Int.castRingHom (ZMod 2)) x).asIdeal := by
  change (↑(2 : ℤ) : ZMod 2) ∈ x.asIdeal
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd 2 2).mpr (by norm_num)]
  exact x.asIdeal.zero_mem

theorem inverseImage_reductionTwo_primeThree :
    (PrimeSpectrum.comap (Int.castRingHom (ZMod 2))) ⁻¹'
        ({primeThree} : Set (PrimeSpectrum ℤ)) = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  intro x hx
  have hEqual : PrimeSpectrum.comap (Int.castRingHom (ZMod 2)) x = primeThree :=
    Set.mem_singleton_iff.mp hx
  have hTwo := two_mem_reduction_comap x
  rw [hEqual] at hTwo
  exact (two_not_mem_primeThree hTwo).elim

/-- The two sides of the printed reduction equality have different values. -/
theorem paper6_proposition7_2_reduction_refuted :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) {primeThree} ≠
      exactDetectionIndex (TopCat.of (PrimeSpectrum (ZMod 2)))
        ((PrimeSpectrum.comap (Int.castRingHom (ZMod 2))) ⁻¹' {primeThree}) := by
  have hZero : exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) {primeThree} = 0 := by
    exact exactDetectionIndex_eq_zero_of_nonempty_closed
      (X := TopCat.of (PrimeSpectrum ℤ)) (P := {primeThree})
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal primeThree).2
        (IsPrime.to_maximal_ideal primeThree_ne_generic))
      (Set.singleton_nonempty primeThree)
  rw [hZero, inverseImage_reductionTwo_primeThree, exactDetectionIndex_empty]
  simp


end

end ManuscriptAudit.SpecIntSupportReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntSupportReduction.three_mem_primeThree,
      ``ManuscriptAudit.SpecIntSupportReduction.two_not_mem_primeThree,
      ``ManuscriptAudit.SpecIntSupportReduction.primeThree_ne_generic,
      ``ManuscriptAudit.SpecIntSupportReduction.two_mem_reduction_comap,
      ``ManuscriptAudit.SpecIntSupportReduction.inverseImage_reductionTwo_primeThree,
      ``ManuscriptAudit.SpecIntSupportReduction.paper6_proposition7_2_reduction_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
