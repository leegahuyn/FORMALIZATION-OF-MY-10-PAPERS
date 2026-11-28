import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaArithmeticInversion
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaMultiplierEuclideanStep
import PrimalitySheafVerification.ManuscriptAudit.Paper8FirstEtaDedekindMultiplier

/-! Identification of the manuscript's Dedekind phase with the actual eta multiplier at every positive lower-left entry. -/

namespace ManuscriptAudit.Paper8ActualEtaDedekindMultiplier

open Matrix
open Paper8EtaPositiveLowerLeftMultiplier Paper8EtaMultiplierEuclideanStep
open Paper8EtaDedekindTranslation Paper8EtaDedekindInversion Paper8EtaArithmeticInversion
open Paper8FirstEtaDedekindMultiplier Paper8OddCrossCuspPhase
open Paper8OddCrossCuspRows (chiFour)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

theorem principalEtaMultiplier_eq_dedekind (g : SL(2, ℤ)) {c : ℕ}
    (hgc : g 1 0 = (c : ℤ)) (hc : 0 < c) :
    principalEtaMultiplier g = explicitEta c (g 0 0) (g 1 1) := by
  refine Nat.strong_induction_on c
    (p := fun n => ∀ u : SL(2, ℤ), u 1 0 = (n : ℤ) → 0 < n →
      principalEtaMultiplier u = explicitEta n (u 0 0) (u 1 1)) ?_ g hgc hc
  intro n ih u hu hn
  have hp : 0 < u 1 0 := by rw [hu]; exact_mod_cast hn
  rcases principalEtaMultiplier_euclidean_step u hp with hOne | ⟨m, hStep⟩
  · have hN : n = 1 := by
      have hInt : (n : ℤ) = 1 := hu.symm.trans hOne
      exact_mod_cast hInt
    rw [hN]
    exact principalEtaMultiplier_eq_explicitEta_of_lowerLeft_one u hOne
  · let U := u * ModularGroup.T ^ m
    let V := U * ModularGroup.S
    change 0 < V 1 0 ∧ V 1 0 < u 1 0 ∧
      principalEtaMultiplier u = (Complex.sqrt Complex.I / translationPhase m) * principalEtaMultiplier V at hStep
    obtain ⟨hVp, hVlt, hV⟩ := hStep
    let d := (V 1 0).toNat
    have hD : (d : ℤ) = V 1 0 := Int.toNat_of_nonneg hVp.le
    have hd : 0 < d := by
      have h : (0 : ℤ) < (d : ℤ) := by rwa [hD]
      exact_mod_cast h
    have hdlt : d < n := by
      have h : (d : ℤ) < (n : ℤ) := by simpa only [hD, hu] using hVlt
      exact_mod_cast h
    have hU0 : U 1 0 = (n : ℤ) := (right_T_entries u m).2.1.trans hu
    have hU1 : U 1 1 = (d : ℤ) := (right_S_entries U).1.symm.trans hD.symm
    have hS : explicitEta d (V 0 0) (V 1 1) =
        explicitEta n (U 0 0) (U 1 1) / Complex.sqrt Complex.I :=
      explicitEta_mul_S U hn hd hU0 hU1
    have hT : explicitEta n (U 0 0) (U 1 1) =
        translationPhase m * explicitEta n (u 0 0) (u 1 1) := by
      obtain ⟨ha, _, hZ⟩ := right_T_entries u m
      change explicitEta n ((u * ModularGroup.T ^ m) 0 0) ((u * ModularGroup.T ^ m) 1 1) = _
      rw [ha, hZ, hu, explicitEta_add_right hn]
    have hI : Complex.sqrt Complex.I ≠ 0 := by
      rw [sqrt_eq_exp Complex.I_ne_zero]
      exact Complex.exp_ne_zero _
    have hE : translationPhase m ≠ 0 := Complex.exp_ne_zero _
    rw [hV, ih d hdlt V hD.symm hd, hS, hT]
    field_simp [hI, hE] <;> ring

theorem principalEtaMultiplier_S_eq_etaAtS : principalEtaMultiplier ModularGroup.S = etaAtS := by
  have hC : ModularGroup.S 1 0 = (1 : ℤ) := by simp [ModularGroup.coe_S]
  have h := principalEtaMultiplier_eq_explicitEta_of_lowerLeft_one ModularGroup.S hC
  have hA : ModularGroup.S 0 0 = (0 : ℤ) := by simp [ModularGroup.coe_S]
  have hD : ModularGroup.S 1 1 = (0 : ℤ) := by simp [ModularGroup.coe_S]
  rw [hA, hD, explicitEta_at_S] at h
  exact h

theorem crossEntry_eq_actualPrincipalEta (g : SL(2, ℤ)) {c : ℕ}
    (hgc : g 1 0 = (c : ℤ)) (hc : 0 < c) :
    crossEntry c (g 0 0) (g 1 1) =
      (chiFour (c : ZMod 4) : ℂ) *
        ((starRingEnd ℂ) (principalEtaMultiplier g / principalEtaMultiplier ModularGroup.S) *
          Complex.exp (periodCoefficient * (scaledCrossDiagonal c (g 0 0) (g 1 1) : ℂ))) := by
  rw [principalEtaMultiplier_eq_dedekind g hgc hc, principalEtaMultiplier_S_eq_etaAtS]
  rfl

end ManuscriptAudit.Paper8ActualEtaDedekindMultiplier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaDedekindMultiplier.principalEtaMultiplier_eq_dedekind,
      ``ManuscriptAudit.Paper8ActualEtaDedekindMultiplier.crossEntry_eq_actualPrincipalEta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
