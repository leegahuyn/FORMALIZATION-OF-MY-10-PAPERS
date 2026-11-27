import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitScalarSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.GeometricSumNearOne
import PrimalitySheafVerification.ManuscriptAudit.EisensteinQuadraticModel
import PrimalitySheafVerification.ManuscriptAudit.AdditiveKernelComposition
import PrimalitySheafVerification.ManuscriptAudit.RotationKernelPrimaryCardinality

/-! The actual first torsion group has square order at every coefficient prime different from the base prime. -/

namespace ManuscriptAudit.CubicSplitLangKernelRank

open CubicCertifiedInertTate CubicNonsplitThreeAdicTrace CubicSplitPrimeFixedCounts
open CubicSplitExtensionTraceRecurrence Paper5NonsplitFrobeniusModFour
open RotationNormUnit EisensteinPowerCongruence EisensteinQuadraticModel
open GeometricSumNearOne TorsionFrobeniusModule AdditiveKernelComposition

noncomputable section
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]

private theorem finite_and_norm (c : IntegralReference p L) (n : ℕ) (hn : 0 < n) :
    let F := arithmeticPointFrobenius (ZMod p) L c.A
    Finite ↥((F ^ n - 1).ker) ∧
      (Nat.card ↥((F ^ n - 1).ker) : ℤ) = ((pair c.a c.b) ^ n - 1).norm := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) c.goodPrime
  obtain ⟨hf, hc⟩ := finite_and_card p L h₂ h₃ c.splitPrime c.nonzeroA n hn
  exact ⟨hf, hc.trans (by rw [norm_pow_sub_one c.a c.b p c.norm, ← c.trace])⟩

/-- A single two-scale Lang comparison gives the true cardinal of E[l],
including coefficient primes split in the Eisenstein integers. -/
theorem card_first (c : IntegralReference p L) (l : ℕ) [Fact l.Prime] (hlp : p ≠ l) :
    Nat.card (Torsion l (Points c)) = l ^ 2 := by
  let G := Points c
  have hPrime : l.Prime := Fact.out
  have hpPrime : p.Prime := Fact.out
  have hc := (Nat.coprime_primes hpPrime hPrime).mpr hlp
  letI : NeZero (l ^ 2) := ⟨pow_ne_zero _ hPrime.ne_zero⟩
  have hUnit : IsUnit ((c.a ^ 2 - c.a * c.b + c.b ^ 2 : ℤ) : ZMod (l ^ 2)) := by
    rw [c.norm, Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right 2)
  obtain ⟨n, hn, ha, hb⟩ := exists_positive_power c.a c.b hUnit
  let v := coefficients c.a c.b n
  have ha' : (↑(l ^ 2) : ℤ) ∣ v.1 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_one, show (v.1 : ZMod (l ^ 2)) = 1 from ha, sub_self]
  have hb' : (↑(l ^ 2) : ℤ) ∣ v.2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  let π := pair c.a c.b
  let z := π ^ n
  have hz : (l : Coefficients) ^ 2 ∣ z - 1 := by
    change (l : Coefficients) ^ 2 ∣ π ^ n - 1
    rw [show π ^ n = pair v.1 v.2 from pair_pow c.a c.b n]
    exact sq_dvd_pair_sub_one l v.1 v.2 (by simpa only [Nat.cast_pow] using ha')
      (by simpa only [Nat.cast_pow] using hb')
  obtain ⟨w, hw⟩ := exists_unit_quotient l z hz
  let u : Coefficients := 1 + (l : Coefficients) * w
  have hGeom : π ^ (n * l) - 1 = ((l : Coefficients) * u) * (z - 1) := by
    change (π ^ (n * l) - 1) = _
    rw [pow_mul]
    change z ^ l - 1 = _
    rw [← geom_sum_mul z l, hw]
  let d := u.norm.toNat
  have hd : (d : ℤ) = u.norm := Int.toNat_of_nonneg (norm_nonneg u)
  have hDvd : ¬ l ∣ d := by
    intro h
    have h0 := (ZMod.natCast_eq_zero_iff d l).mpr h
    have h1 : (d : ZMod l) = 1 := by
      rw [← Int.cast_natCast, hd]
      exact norm_one_add_cast_mod l w
    exact zero_ne_one (h0.symm.trans h1)
  have hNorm : (π ^ (n * l) - 1).norm = ((l ^ 2 * d : ℕ) : ℤ) * (z - 1).norm := by
    rw [hGeom, map_mul, map_mul, QuadraticAlgebra.norm_natCast, Nat.cast_mul, Nat.cast_pow, hd]
  let act := EisensteinQuadraticModel.action c.rotation c.quadratic
  let F := arithmeticPointFrobenius (ZMod p) L c.A
  let S : AddMonoid.End G := l • combination c.rotation u.re u.im
  have hAct : act π = F := (action_pair c.rotation c.quadratic c.a c.b).trans c.native.symm
  have hEnd : F ^ (n * l) - 1 = S * (F ^ n - 1) := by
    have h := congrArg act hGeom
    simp only [map_sub, map_pow, map_mul, map_natCast, map_one, hAct] at h
    have hU : (l : AddMonoid.End G) * act u = S := by
      rw [action_eq_combination, nsmul_eq_mul]
    rw [hU] at h
    exact h
  let f := F ^ n - 1
  let g := F ^ (n * l) - 1
  have hK : g = S.comp f := hEnd
  obtain ⟨hFin, hCount⟩ := finite_and_norm c n hn
  obtain ⟨hFin', hCount'⟩ := finite_and_norm c (n * l) (Nat.mul_pos hn hPrime.pos)
  letI : Finite ↥f.ker := hFin
  have hPos : (Nat.card ↥f.ker : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr Nat.card_pos.ne'
  have hs : Function.Surjective f :=
    CubicLangPowers.pow_sub_one_surjective p L c.goodPrime c.nonzeroA hn
  have hC : Nat.card ↥g.ker = Nat.card ↥S.ker * Nat.card ↥f.ker := by
    rw [hK]
    exact card_ker_comp S f hs
  have hFinite : Finite ↥(S.comp f).ker := hK ▸ hFin'
  letI : Finite ↥(S.comp f).ker := hFinite
  have hFinS : Finite ↥S.ker :=
    Finite.of_surjective (restriction S f) (restriction_surjective S f hs)
  have hC' : (Nat.card ↥g.ker : ℤ) = (Nat.card ↥S.ker : ℤ) * (Nat.card ↥f.ker : ℤ) := by
    exact_mod_cast hC
  have hRatio : (Nat.card ↥S.ker : ℤ) = ((l ^ 2 * d : ℕ) : ℤ) := by
    apply mul_right_cancel₀ hPos
    calc
      _ = (Nat.card ↥g.ker : ℤ) := hC'.symm
      _ = (π ^ (n * l) - 1).norm := hCount'
      _ = _ := by rw [hNorm, ← hCount]
  have hRatio' : Nat.card ↥S.ker = l ^ 2 * d := by exact_mod_cast hRatio
  have hd' : (d : ℤ) = u.re ^ 2 - u.re * u.im + u.im ^ 2 := hd.trans (norm_eq u)
  have hResult := RotationKernelPrimaryCardinality.card_torsion_of_kernel l 1 d
    c.rotation c.quadratic u.re u.im hd' hDvd
    (by simpa only [pow_one] using hFinS) (by simpa only [pow_one] using hRatio')
  simpa only [pow_one] using hResult

end

end ManuscriptAudit.CubicSplitLangKernelRank

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitLangKernelRank.card_first
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
