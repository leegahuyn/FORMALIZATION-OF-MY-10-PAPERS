import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularRelativeTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5RelativeNonsplitTateTrace

/-! Genuine prime-adic power traces over every finite field of the supersingular family. -/

namespace ManuscriptAudit.CubicSupersingularAllFiniteFields

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open PowerTateModule CubicNonsplitThreeAdicTrace Paper5LinearTraceRecurrence

noncomputable section

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]
variable (F E L : Type*) [Field F] [Field E] [Field L]
variable [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E] [DecidableEq L]
variable [Algebra (ZMod p) F] [Algebra (ZMod p) E] [Algebra (ZMod p) L]
variable [CharP F p] [CharP E p] [Algebra F E] [IsScalarTower (ZMod p) F E]
variable [Algebra F L] [Algebra E L] [IsScalarTower F E L]
variable [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]

private theorem half_degree_positive {m : ℕ} (hm : Module.finrank (ZMod p) F = 2 * m) :
    0 < m := by
  by_contra h
  have hz : m = 0 := by omega
  have hc : Fintype.card F = p ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := F), ZMod.card, hm]
  rw [hz, mul_zero, pow_zero] at hc
  exact (ne_of_gt (Fintype.one_lt_card : 1 < Fintype.card F)) hc

theorem arithmetic_power_trace (hp : 5 ≤ p) (hP : p % 3 = 2) (hℓ : ℓ ≠ p)
    {a : F} (ha : a ≠ 0) :
    LinearMap.trace ℤ_[ℓ] (Tate ℓ (GeometricPoints F L a))
      ((endMap ℓ (arithmeticPointFrobenius F L a)) ^ Module.finrank F E) =
    (Int.cast ((Fintype.card E : ℤ) + 1 -
      (Nat.card (shortCubic (0 : E) (algebraMap F E a)).toProjective.Point : ℤ)) : ℤ_[ℓ]) := by
  let d := Module.finrank (ZMod p) F
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨m, hm⟩ := he
    have hm' : Module.finrank (ZMod p) F = 2 * m := by
      change d = 2 * m
      omega
    exact CubicSupersingularRelativeTrace.trace_pow_eq_point_count
      p L ℓ F E hp hP hℓ hm' (half_degree_positive p F hm') ha
  · have hQ : Fintype.card F % 3 = 2 :=
      CubicOddExtensionTrace.odd_extension_card_mod_three (E := F) hP ho
    obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
    have h₂ : (2 : F) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₂p
    have h₃ : (3 : F) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₃p
    let B := CubicNonsplitFiniteFieldTate.actualBasis p L ℓ F hp hP hℓ h₂ h₃ ha
    let T := endMap ℓ (arithmeticPointFrobenius F L a)
    have hd : LinearMap.det T = (Fintype.card F : ℤ_[ℓ]) :=
      CubicNonsplitFiniteFieldTate.determinant p L ℓ F hp hP hℓ h₂ h₃ ha hQ
    have ht : LinearMap.trace ℤ_[ℓ] (Tate ℓ (GeometricPoints F L a)) T = 0 :=
      actual_prime_adic_trace_zero F L ℓ h₂ h₃ ha hQ
    have hPow := trace_pow_eq_recurrence B T (Fintype.card F) 0
      (by simpa only [Int.cast_zero] using ht) hd (Module.finrank F E)
    have hCount := Paper5RelativeNonsplitCounts.signed_counts p F E hp hP hQ ha
    exact hPow.trans (congrArg (fun t : ℤ => (t : ℤ_[ℓ])) hCount).symm

/-- The determinant on the genuine Tate module equals the cardinality of any finite base. -/
theorem arithmetic_determinant (hp : 5 ≤ p) (hP : p % 3 = 2) (hℓ : ℓ ≠ p)
    {a : F} (ha : a ≠ 0) :
    LinearMap.det (endMap ℓ (arithmeticPointFrobenius F L a)) = (Fintype.card F : ℤ_[ℓ]) := by
  let d := Module.finrank (ZMod p) F
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨m, hm⟩ := he
    have hm' : Module.finrank (ZMod p) F = 2 * m := by
      change d = 2 * m
      omega
    exact (CubicSupersingularTatePointCount.trace_det_eq_point_count
      p L ℓ F hp hP hℓ hm' (half_degree_positive p F hm') ha).2
  · have hQ : Fintype.card F % 3 = 2 :=
      CubicOddExtensionTrace.odd_extension_card_mod_three (E := F) hP ho
    obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
    have h₂ : (2 : F) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₂p
    have h₃ : (3 : F) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) F)).mpr h₃p
    exact CubicNonsplitFiniteFieldTate.determinant p L ℓ F hp hP hℓ h₂ h₃ ha hQ

/-- The two coefficients of the actual characteristic polynomial have their exact arithmetic values. -/
theorem arithmetic_charpoly (hp : 5 ≤ p) (hP : p % 3 = 2) (hℓ : ℓ ≠ p)
    {a : F} (ha : a ≠ 0) :
    let B := CubicSupersingularTatePointCount.tateBasis p L ℓ F hp hP hℓ ha
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    let T := endMap ℓ (arithmeticPointFrobenius F L a)
    T.charpoly = Polynomial.X ^ 2 - Polynomial.C
      (Int.cast ((Fintype.card F : ℤ) + 1 -
        (Nat.card (shortCubic (0 : F) a).toProjective.Point : ℤ)) : ℤ_[ℓ]) * Polynomial.X +
      Polynomial.C (Fintype.card F : ℤ_[ℓ]) := by
  let B := CubicSupersingularTatePointCount.tateBasis p L ℓ F hp hP hℓ ha
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let T := endMap ℓ (arithmeticPointFrobenius F L a)
  have ht : LinearMap.trace ℤ_[ℓ] (Tate ℓ (GeometricPoints F L a)) T =
      (Int.cast ((Fintype.card F : ℤ) + 1 -
        (Nat.card (shortCubic (0 : F) a).toProjective.Point : ℤ)) : ℤ_[ℓ]) := by
    simpa only [Module.finrank_self, pow_one, Algebra.algebraMap_self_apply] using
      arithmetic_power_trace p ℓ F F L hp hP hℓ ha
  have hd : LinearMap.det T = (Fintype.card F : ℤ_[ℓ]) :=
    arithmetic_determinant p ℓ F L hp hP hℓ ha
  change T.charpoly = _
  rw [← LinearMap.charpoly_toMatrix T B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[ℓ] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.CubicSupersingularAllFiniteFields

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularAllFiniteFields.arithmetic_power_trace,
      ``ManuscriptAudit.CubicSupersingularAllFiniteFields.arithmetic_determinant,
      ``ManuscriptAudit.CubicSupersingularAllFiniteFields.arithmetic_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
