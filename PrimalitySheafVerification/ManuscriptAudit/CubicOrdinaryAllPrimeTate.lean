import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinaryAllPrimeTateRank
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationNoScalarTate
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! Native Frobenius for every ordinary centered twist over every finite field
has its actual arithmetic Tate coefficients for all coefficient primes away from the characteristic. -/

namespace ManuscriptAudit.CubicOrdinaryAllPrimeTate

open Polynomial Module PowerTorsionTower TorsionFrobeniusModule PowerTateModule
open CubicNonsplitThreeAdicTrace CubicSplitIntegralFrobenius CubicThreeFrobeniusSigns
open CubicNaturalCMOperations CubicRotationNoScalarTate RotationNormUnit
open CubicFrobeniusTranscendentalRelation Paper5NonsplitFrobeniusModFour
open CubicSplitExtensionTraceRecurrence
open scoped Padic

noncomputable section
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (E L : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
  [DecidableEq E] [Field L] [Algebra E L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]
variable (l : ℕ) [Fact l.Prime]

abbrev actual (A : E) : Module.End ℤ_[l] (Tate l (GeometricPoints E L A)) :=
  endMap l (arithmeticPointFrobenius E L A)

private theorem card_mod_three (hs : p % 3 = 1) : Fintype.card E % 3 = 1 := by
  have hpow (n : ℕ) : p ^ n % 3 = 1 := by
    induction n with
    | zero => rw [pow_zero]; decide
    | succ n hn => rw [pow_succ, Nat.mul_mod, hn, hs] <;> decide
  have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := E)
  rw [ZMod.card] at hc
  rw [hc]
  exact hpow _

/-- Every actual ordinary twist has the exact signed point count and field size as its Tate coefficients. -/
theorem trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual E L l A) = (arithmeticTrace E A : ℤ_[l]) ∧
      LinearMap.det (actual E L l A) = (Fintype.card E : ℤ_[l]) := by
  let G := GeometricPoints E L A
  let B := CubicOrdinaryAllPrimeTateRank.basis p E L l hp hs hA hl
  obtain ⟨hCard, hDiv⟩ := CubicOrdinaryAllPrimeTateRank.card_and_scalar_surjective
    p E L l hp hs hA hl
  let B₀ := FirstPrimeTorsionBasis.basis l G (by simpa only [pow_one] using hCard 1)
  obtain ⟨h₂P, h₃P⟩ := small_char p (ZMod p) hp
  have h₂ : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₂P
  have h₃ : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₃P
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL := (map_ne_zero (algebraMap E L)).mpr hA
  have hChar : ringChar E ≠ 2 := by
    intro h
    exact h₂ ((ringChar.spec E 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  have hEq := card_mod_three p E hs
  have hSplit : 3 ∣ Fintype.card E - 1 := by omega
  obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root hEq
  let r : AddMonoid.End G := (rotation h₂ h₃ hA hz.pow_eq_one).atField L
  have hQuad : r ^ 2 + r + 1 = 0 := rotation_quadratic h₂ h₃ hA hz.pow_eq_one L
    (hz.ne_one (by decide))
  obtain ⟨a, b, ht, hn, he⟩ := exists_integral_combination (L := L) h₂ h₃ hChar hSplit hA
    hz.pow_eq_one (hz.ne_one (by decide))
  have hZ : (algebraMap E L z) ^ 3 = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
  have hZ₁ : algebraMap E L z ≠ 1 := by
    intro h
    apply hz.ne_one (by decide)
    apply (algebraMap E L).injective
    rw [map_one, h]
  have hR : (rotation h₂L h₃L hAL hZ).atField L = r := rfl
  have hNot : ¬ ∃ w : ℤ_[l], endMap l r =
      w • (1 : Module.End ℤ_[l] (Tate l G)) := by
    rw [← hR]
    exact rotation_not_scalar L h₂L h₃L hAL hZ hZ₁ l B₀ hDiv (hCard 2)
  let S := endMap l r
  have hS : S ^ 2 + S + 1 = 0 := by
    simpa only [S, map_pow, map_add, map_one, map_zero] using congrArg (endMap l) hQuad
  let J : Module.End ℤ_[l] (Tate l G) := 1
  have hComb : actual E L l A = (a : ℤ_[l]) • J + (b : ℤ_[l]) • S := by
    have hm := congrArg (endMap l) he
    change actual E L l A = endMap l (a • (1 : AddMonoid.End G) + b • r) at hm
    rw [map_add, map_zsmul, map_zsmul, map_one,
      ← Int.cast_smul_eq_zsmul ℤ_[l] a J, ← Int.cast_smul_eq_zsmul ℤ_[l] b S] at hm
    exact hm
  have h := CubicTateRotationCoefficients.trace_det_linear B S hNot hS (a : ℤ_[l]) (b : ℤ_[l])
  rw [hComb]
  have h' :
      LinearMap.trace ℤ_[l] _ ((a : ℤ_[l]) • J + (b : ℤ_[l]) • S) =
        ((2 * a - b : ℤ) : ℤ_[l]) ∧
      LinearMap.det ((a : ℤ_[l]) • J + (b : ℤ_[l]) • S) =
        ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) := by
    simpa only [J, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using h
  rw [← ht, hn, Int.cast_natCast] at h'
  exact h'

/-- The genuine characteristic polynomial over the full native Tate module. -/
theorem charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    let B := CubicOrdinaryAllPrimeTateRank.basis p E L l hp hs hA hl
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (actual E L l A).charpoly =
      X ^ 2 - C (arithmeticTrace E A : ℤ_[l]) * X + C (Fintype.card E : ℤ_[l]) := by
  let B := CubicOrdinaryAllPrimeTateRank.basis p E L l hp hs hA hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det p E L l hp hs hA hl
  change (actual E L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

/-- The powers of the same actual geometric operator realize the counts over all further extensions. -/
theorem extension_trace (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra E F]
    (hp : 5 ≤ p) (hs : p % 3 = 1) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual E L l A ^ finrank E F) =
      (signedTrace (algebraMap E F A) : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det p E L l hp hs hA hl
  obtain ⟨h₂P, h₃P⟩ := small_char p (ZMod p) hp
  have h₂ : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₂P
  have h₃ : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₃P
  have hEq := card_mod_three p E hs
  have hSplit : 3 ∣ Fintype.card E - 1 := by omega
  have he := extension_trace_eq_recurrence (E := F) h₂ h₃ hA hSplit
  have h := Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
    (CubicOrdinaryAllPrimeTateRank.basis p E L l hp hs hA hl) (actual E L l A)
    (Fintype.card E) (arithmeticTrace E A) ht hd (finrank E F)
  exact h.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) he.symm)

end

end ManuscriptAudit.CubicOrdinaryAllPrimeTate

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTate.trace_det,
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTate.charpoly,
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTate.extension_trace] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
