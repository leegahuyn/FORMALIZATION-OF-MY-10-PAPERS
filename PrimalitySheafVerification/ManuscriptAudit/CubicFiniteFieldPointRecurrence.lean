import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularAllFiniteFields
import PrimalitySheafVerification.ManuscriptAudit.CubicTraceClassification

/-! The exact recurrence of genuine projective point counts over any good finite base. -/

namespace ManuscriptAudit.CubicFiniteFieldPointRecurrence

open Module FiniteFieldPointCount CubicSplitExtensionTraceRecurrence
open CubicNonsplitThreeAdicTrace PowerTateModule
open Paper5PrintedRecurrence
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] [CharP E p]

private theorem divisible_card_sub_one (hs : p % 3 = 1) : 3 ∣ Fintype.card E - 1 := by
  have hpow (n : ℕ) : p ^ n % 3 = 1 := by
    induction n with
    | zero => rw [pow_zero]; decide
    | succ n hn => rw [pow_succ, Nat.mul_mod, hn, hs] <;> decide
  have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := E)
  rw [ZMod.card] at hc
  have h := hpow (finrank (ZMod p) E)
  rw [← hc] at h
  omega

/-- Over every actual finite extension of a good centered cubic, the signed count has the exact scalar recurrence. -/
theorem extension_trace (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra E D]
    [Algebra (ZMod p) D] [CharP D p] [IsScalarTower (ZMod p) E D]
    (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) :
    signedTrace (algebraMap E D A) =
      recurrence (Fintype.card E) (signedTrace A) (finrank E D) := by
  classical
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · let L := AlgebraicClosure D
    letI : FiniteDimensional (ZMod p) D := Module.Finite.of_finite
    letI : Algebra.IsAlgebraic (ZMod p) L := Algebra.IsAlgebraic.trans (ZMod p) D L
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hl : (2 : ℕ) ≠ p := by omega
    let B := CubicSupersingularTatePointCount.tateBasis p L 2 E hp hn hl hA
    let T : Module.End ℤ_[2] (Tate 2 (GeometricPoints E L A)) :=
      endMap 2 (arithmeticPointFrobenius E L A)
    have ht : LinearMap.trace ℤ_[2] _ T = (signedTrace A : ℤ_[2]) := by
      simpa only [T, signedTrace, finrank_self, pow_one, Algebra.algebraMap_self_apply] using
        (CubicSupersingularAllFiniteFields.arithmetic_power_trace p 2 E E L hp hn hl hA)
    have hd : LinearMap.det T = (Fintype.card E : ℤ_[2]) :=
      CubicSupersingularAllFiniteFields.arithmetic_determinant p 2 E L hp hn hl hA
    have hSigned : LinearMap.trace ℤ_[2] _ (T ^ finrank E D) =
        (signedTrace (algebraMap E D A) : ℤ_[2]) := by
      simpa only [T, signedTrace] using
        (CubicSupersingularAllFiniteFields.arithmetic_power_trace p 2 E D L hp hn hl hA)
    have hRec := Paper5LinearTraceRecurrence.trace_pow_eq_recurrence B T
      (Fintype.card E) (signedTrace A) ht hd (finrank E D)
    exact_mod_cast hSigned.symm.trans hRec
  · have hs : p % 3 = 1 := by omega
    obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
    have h₂ : (2 : E) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₂p
    have h₃ : (3 : E) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₃p
    exact extension_trace_eq_recurrence (E := D) h₂ h₃ hA (divisible_card_sub_one p E hs)

/-- Term n counts points over Mathlib's genuine extension of degree n+1. -/
def pointCount (A : E) (n : ℕ) : ℕ :=
  letI : NeZero (n+1) := ⟨Nat.succ_ne_zero n⟩
  let D := FiniteField.Extension E p (n+1)
  Nat.card (shortCubic (0 : D) (algebraMap E D A)).toProjective.Point

theorem pointCount_eq_recurrence (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (n : ℕ) :
    (pointCount p E A n : ℤ) =
      ((Fintype.card E ^ (n+1) : ℕ) : ℤ) + 1 -
        recurrence (Fintype.card E) (signedTrace A) (n+1) := by
  classical
  letI : NeZero (n+1) := ⟨Nat.succ_ne_zero n⟩
  let D := FiniteField.Extension E p (n+1)
  letI : Fintype D := Fintype.ofFinite D
  letI : CharP D p := charP_of_injective_algebraMap (algebraMap E D).injective p
  have h := extension_trace p E D hp hA
  change (Fintype.card D : ℤ) + 1 - (pointCount p E A n : ℤ) =
    recurrence (Fintype.card E) (signedTrace A) (finrank E D) at h
  have hCard : Fintype.card D = Fintype.card E ^ (n+1) := by
    rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension,
      ← Fintype.card_eq_nat_card]
  have hDegree : finrank E D = n+1 := FiniteField.finrank_extension E p (n+1)
  rw [hCard, hDegree] at h
  linarith

/-- The chosen extension count equals the count on every actual extension of the same degree. -/
theorem pointCount_eq_extension (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra E D]
    [Algebra (ZMod p) D] [CharP D p] [IsScalarTower (ZMod p) E D]
    (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) {n : ℕ} (hD : finrank E D = n+1) :
    pointCount p E A n =
      Nat.card (shortCubic (0 : D) (algebraMap E D A)).toProjective.Point := by
  have h := extension_trace p E D hp hA
  have hc := Module.card_eq_pow_finrank (K := E) (V := D)
  rw [hD] at h hc
  have h' := pointCount_eq_recurrence p E hp hA n
  change (Fintype.card D : ℤ) + 1 -
    (Nat.card (shortCubic (0 : D) (algebraMap E D A)).toProjective.Point : ℤ) =
    recurrence (Fintype.card E) (signedTrace A) (n+1) at h
  rw [hc] at h
  have hEq : (pointCount p E A n : ℤ) =
      (Nat.card (shortCubic (0 : D) (algebraMap E D A)).toProjective.Point : ℤ) := by
    linarith
  exact_mod_cast hEq

end
end ManuscriptAudit.CubicFiniteFieldPointRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFiniteFieldPointRecurrence.extension_trace,
      ``ManuscriptAudit.CubicFiniteFieldPointRecurrence.pointCount_eq_recurrence,
      ``ManuscriptAudit.CubicFiniteFieldPointRecurrence.pointCount_eq_extension] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
