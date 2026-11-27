import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitAllPrimeTateRank
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationNoScalarTate
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! At every good split base prime, the native Tate Frobenius has its exact arithmetic
characteristic polynomial for every coefficient prime away from the base characteristic. -/

namespace ManuscriptAudit.CubicSplitAllPrimeTate

open Polynomial Module PowerTorsionTower TorsionFrobeniusModule PowerTateModule
open CubicNonsplitThreeAdicTrace CubicSplitAllPrimeTateRank CubicSplitAllInertTate
open CubicSplitExtensionTraceRecurrence CubicSplitIntegralFrobenius CubicThreeFrobeniusSigns
open CubicNaturalCMOperations CubicRotationNoScalarTate RotationNormUnit
open CubicFrobeniusTranscendentalRelation Paper5NonsplitFrobeniusModFour
open scoped Padic

noncomputable section
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]
variable (l : ℕ) [Fact l.Prime]

abbrev actual (A : ZMod p) : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  endMap l (arithmeticPointFrobenius (ZMod p) L A)

/-- The exact signed point-count trace and determinant p at every coefficient prime l≠p. -/
theorem trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual p L l A) = (arithmeticTrace (ZMod p) A : ℤ_[l]) ∧
      LinearMap.det (actual p L l A) = (p : ℤ_[l]) := by
  let G := GeometricPoints (ZMod p) L A
  let B := nativeBasis (L := L) hp hs hA l hl
  let c := reference p L hp hs hA
  have hPrime : l.Prime := Fact.out
  have hpPrime : p.Prime := Fact.out
  have hc := (Nat.coprime_primes hpPrime hPrime).mpr hl
  have hDiv : Function.Surjective (fun P : G => l • P) :=
    CubicSplitScalarSurjectivity.scalar_surjective_of_reference c hPrime.ne_zero hc
  have hCard : ∀ n, Nat.card (PowerTorsion l G n) = (l ^ 2) ^ n :=
    (CubicSplitAllPrimeTateRank.card_and_transition c l hl).1
  let B₀ := FirstPrimeTorsionBasis.basis l G (by simpa only [pow_one] using hCard 1)
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃
  have hAL := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  have hChar : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hCard₀ : Fintype.card (ZMod p) % 3 = 1 := by rw [ZMod.card]; exact hs
  have hSplit : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root hCard₀
  let r : AddMonoid.End G := (rotation h₂ h₃ hA hz.pow_eq_one).atField L
  have hQuad : r ^ 2 + r + 1 = 0 := rotation_quadratic h₂ h₃ hA hz.pow_eq_one L
    (hz.ne_one (by decide))
  obtain ⟨a, b, ht, hn, he⟩ := exists_integral_combination (L := L) h₂ h₃ hChar hSplit hA
    hz.pow_eq_one (hz.ne_one (by decide))
  have hZ : (algebraMap (ZMod p) L z) ^ 3 = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
  have hZ₁ : algebraMap (ZMod p) L z ≠ 1 := by
    intro h
    apply hz.ne_one (by decide)
    apply (algebraMap (ZMod p) L).injective
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
  have hComb : actual p L l A = (a : ℤ_[l]) • J + (b : ℤ_[l]) • S := by
    have hm := congrArg (endMap l) he
    change actual p L l A = endMap l (a • (1 : AddMonoid.End G) + b • r) at hm
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
  rw [← ht, hn, ZMod.card, Int.cast_natCast] at h'
  exact h'

/-- The characteristic polynomial is genuinely that of the native Tate endomorphism. -/
theorem charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    let B := nativeBasis (L := L) hp hs hA l hl
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (actual p L l A).charpoly = X ^ 2 - C (arithmeticTrace (ZMod p) A : ℤ_[l]) * X + C (p : ℤ_[l]) := by
  let B := nativeBasis (L := L) hp hs hA l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det p L l hp hs hA hl
  change (actual p L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (actual p L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

/-- The actual Frobenius power traces agree with all finite extension point counts. -/
theorem extension_trace (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual p L l A ^ finrank (ZMod p) E) =
      (signedTrace (algebraMap (ZMod p) E A) : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det p L l hp hs hA hl
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hSplit : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  have he := extension_trace_eq_recurrence (E := E) h₂ h₃ hA hSplit
  rw [ZMod.card] at he
  have h := Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
    (nativeBasis (L := L) hp hs hA l hl) (actual p L l A) p
    (arithmeticTrace (ZMod p) A) ht hd (finrank (ZMod p) E)
  exact h.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) he.symm)

end

end ManuscriptAudit.CubicSplitAllPrimeTate

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitAllPrimeTate.trace_det,
      ``ManuscriptAudit.CubicSplitAllPrimeTate.charpoly,
      ``ManuscriptAudit.CubicSplitAllPrimeTate.extension_trace] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
