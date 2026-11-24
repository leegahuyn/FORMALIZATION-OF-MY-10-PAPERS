import Mathlib

open scoped Matrix

namespace ManuscriptAudit

/-- Paper 3, pp. 60–62 and 82. The prime 2 misses the printed numeric
window for every integer base and every exponent of at least two. -/
theorem paper3_prime_two_misses_numeric_window :
    Nat.Prime 2 ∧ ∀ (A : ℤ) (q : ℕ), 2 ≤ q →
      ¬ |(2 : ℝ) - (A : ℝ) ^ q| ≤ (A : ℝ) / q := by
  refine ⟨Nat.prime_two, ?_⟩
  intro A q hq
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < (q : ℝ) := by linarith
  apply not_le.mpr
  by_cases hA : 0 < A
  · by_cases hOne : A = 1
    · subst A
      have hdiv : (1 : ℝ) / q < 1 :=
        (div_lt_iff₀ hqPos).mpr (by linarith)
      simpa using hdiv
    · have hA2 : (2 : ℝ) ≤ (A : ℝ) := by
        exact_mod_cast (show (2 : ℤ) ≤ A by omega)
      have hPow : (A : ℝ) ^ 2 ≤ (A : ℝ) ^ q :=
        pow_le_pow_right₀ (by linarith) hq
      have hSize : (A : ℝ) ≤ (A : ℝ) ^ q - 2 := by
        nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) - 2 by linarith)
          (show 0 ≤ (A : ℝ) + 1 by linarith)]
      have hdiv : (A : ℝ) / q < (A : ℝ) :=
        (div_lt_iff₀ hqPos).mpr (by
          nlinarith [mul_pos (show 0 < (A : ℝ) by linarith)
            (show 0 < (q : ℝ) - 1 by linarith)])
      rw [abs_of_nonpos (by linarith)]
      linarith
  · by_cases hZero : A = 0
    · subst A
      have hqNe : q ≠ 0 := by omega
      norm_num [zero_pow hqNe]
    · have hNeg : (A : ℝ) < 0 := by
        exact_mod_cast (show A < (0 : ℤ) by omega)
      exact lt_of_lt_of_le (div_neg_of_neg_of_pos hNeg hqPos) (abs_nonneg _)

private def liftExampleCurve (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨0, 0, 0, -1, 1⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def IsLiftOfExamplePoint (P : ℤ_[5] × ℤ_[5]) : Prop :=
  (liftExampleCurve ℤ_[5]).toAffine.Equation P.1 P.2 ∧
    PadicInt.toZMod (p := 5) P.1 = 0 ∧ PadicInt.toZMod (p := 5) P.2 = 1

/-- Paper 2, p. 37, Remark 3.14. A smooth residue point at a good prime
has two distinct lifts on the same Weierstrass curve. -/
theorem paper2_good_reduction_does_not_give_unique_point_lifts :
    ¬ (5 : ℤ) ∣ (liftExampleCurve ℤ).Δ ∧
      (liftExampleCurve (ZMod 5)).toAffine.Nonsingular 0 1 ∧
      ¬ ∃! P, IsLiftOfExamplePoint P := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [liftExampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · rw [WeierstrassCurve.Affine.nonsingular_iff',
      WeierstrassCurve.Affine.equation_iff]
    change (1 : ZMod 5) ^ 2 + 0 * 0 * 1 + 0 * 1 =
      0 ^ 3 + 0 * 0 ^ 2 + (-1) * 0 + 1 ∧
      (0 * 1 - (3 * 0 ^ 2 + 2 * 0 * 0 + (-1)) ≠ 0 ∨
        2 * 1 + 0 * 0 + 0 ≠ 0)
    decide
  · have h₀ : IsLiftOfExamplePoint (0, 1) := by
      refine ⟨?_, map_zero _, map_one _⟩
      rw [WeierstrassCurve.Affine.equation_iff]
      norm_num [liftExampleCurve]
    have h₁ : IsLiftOfExamplePoint (5, 11) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        norm_num [liftExampleCurve]
      · calc
          PadicInt.toZMod (p := 5) (5 : ℤ_[5]) = ((5 : ℕ) : ZMod 5) :=
            map_natCast _ 5
          _ = 0 := by decide
      · calc
          PadicInt.toZMod (p := 5) (11 : ℤ_[5]) = ((11 : ℕ) : ZMod 5) :=
            map_natCast _ 11
          _ = 1 := by decide
    rintro ⟨P, _, hUnique⟩
    have hEq := (hUnique (0, 1) h₀).trans (hUnique (5, 11) h₁).symm
    have hX : (0 : ℤ_[5]) = 5 := congrArg Prod.fst hEq
    norm_num at hX

/-- Papers 2 and 6, pp. 37 and 191. The coprime principal opens
at 2 and 3 have a point omitted by their overlap D(6). -/
theorem coprime_principal_open_union_ne_product_open :
    PrimeSpectrum.basicOpen (2 : ℤ) ⊔ PrimeSpectrum.basicOpen 3 ≠
      PrimeSpectrum.basicOpen 6 := by
  let x : PrimeSpectrum ℤ :=
    ⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime (by norm_num)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two)⟩
  have h3 : x ∈ PrimeSpectrum.basicOpen (3 : ℤ) := by
    rw [PrimeSpectrum.mem_basicOpen]
    change (3 : ℤ) ∉ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    norm_num
  have h6 : x ∉ PrimeSpectrum.basicOpen (6 : ℤ) := by
    rw [PrimeSpectrum.mem_basicOpen, not_not]
    change (6 : ℤ) ∈ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    norm_num
  intro h
  apply h6
  rw [← h]
  exact (le_sup_right :
    PrimeSpectrum.basicOpen (3 : ℤ) ≤
      PrimeSpectrum.basicOpen 2 ⊔ PrimeSpectrum.basicOpen 3) h3

/-- Paper 8, p. 348, G.0.1. The displayed matrix and the displayed
Bézout equation cannot both hold for every reduced cusp. -/
theorem paper8_printed_cusp_representative_false :
    ¬ ∀ k h : ℤ, 1 ≤ k → 0 ≤ h → h < k →
      Nat.Coprime h.natAbs k.natAbs →
      ∃ a b : ℤ,
        (!![a, b; k, -h] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
          a * h - b * k = 1 := by
  intro hRep
  have hgcd : Nat.Coprime (Int.natAbs (1 : ℤ)) (Int.natAbs (2 : ℤ)) := by decide
  obtain ⟨a, b, hDet, hBezout⟩ :=
    hRep 2 1 (by norm_num) (by norm_num) (by norm_num) hgcd
  have hDet' : a * (-(1 : ℤ)) - b * 2 = 1 := by
    simpa only [Matrix.det_fin_two_of] using hDet
  have hBezout' : a - b * 2 = 1 := by simpa only [mul_one] using hBezout
  rw [mul_neg, mul_one] at hDet'
  omega

private def truncationTerm (c : ℕ) : ℝ :=
  if c = 2 then 1 else if c = 3 then -1 else 0

private def truncationCut (K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range K, truncationTerm (c + 1)

/-- Paper 8, pp. 351 and 354, D3. The exact tail identity alone does
not imply the displayed truncation-doubling error bound. -/
theorem paper8_doubling_bound_does_not_follow_from_tail_identity :
    ∃ a aK a2K EK E2K : ℝ,
      a = aK + EK ∧ a = a2K + E2K ∧ ¬ |a2K - aK| ≤ |EK| := by
  refine ⟨truncationCut 3, truncationCut 1, truncationCut (2 * 1),
    truncationCut 3 - truncationCut 1, truncationCut 3 - truncationCut (2 * 1),
    ?_, ?_, ?_⟩
  · ring
  · ring
  · norm_num [truncationCut, truncationTerm, Finset.sum_range_succ]

private def scaledIntCast {L : ℕ} (c : ZMod L) : ℤ →+ ZMod L where
  toFun x := c * (x : ZMod L)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private def cyclicInclusion {L : ℕ} (d : ℕ) (c : ZMod L)
    (h : c * (d : ZMod L) = 0) : ZMod d →+ ZMod L :=
  ZMod.lift d ⟨scaledIntCast c, by
    change c * ((d : ℤ) : ZMod L) = 0
    simpa only [Int.cast_natCast] using h⟩

private theorem cyclicInclusion_int {L : ℕ} (d : ℕ) (c : ZMod L)
    (h : c * (d : ZMod L) = 0) (x : ℤ) :
    cyclicInclusion d c h (x : ZMod d) = c * (x : ZMod L) := by
  unfold cyclicInclusion
  exact ZMod.lift_coe d _ x

private def inclusionDifference {m n L : ℕ}
    (f : ZMod m →+ ZMod L) (g : ZMod n →+ ZMod L) :
    (ZMod m × ZMod n) →+ ZMod L :=
  f.comp (AddMonoidHom.fst _ _) - g.comp (AddMonoidHom.snd _ _)

private def cechSixNine : (ZMod 6 × ZMod 9) →+ ZMod 18 :=
  inclusionDifference (cyclicInclusion 6 3 (by decide))
    (cyclicInclusion 9 2 (by decide))

private def cechSixTen : (ZMod 6 × ZMod 10) →+ ZMod 30 :=
  inclusionDifference (cyclicInclusion 6 5 (by decide))
    (cyclicInclusion 10 3 (by decide))

private theorem cechSixNine_surjective : Function.Surjective cechSixNine := by
  intro r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := 18) r
  refine ⟨((x : ZMod 6), (x : ZMod 9)), ?_⟩
  change cyclicInclusion 6 3 _ (x : ZMod 6) -
    cyclicInclusion 9 2 _ (x : ZMod 9) = (x : ZMod 18)
  rw [cyclicInclusion_int, cyclicInclusion_int]
  ring

private theorem cechSixTen_surjective : Function.Surjective cechSixTen := by
  intro r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := 30) r
  refine ⟨(((2 * x : ℤ) : ZMod 6), ((3 * x : ℤ) : ZMod 10)), ?_⟩
  change cyclicInclusion 6 5 _ ((2 * x : ℤ) : ZMod 6) -
    cyclicInclusion 10 3 _ ((3 * x : ℤ) : ZMod 10) = (x : ZMod 30)
  rw [cyclicInclusion_int, cyclicInclusion_int]
  push_cast
  ring

private theorem noEquivOfSurjectiveDifference {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [Nontrivial P] (f : M →+ N)
    (hf : Function.Surjective f) : ¬ Nonempty ((N ⧸ f.range) ≃ P) := by
  have hTop : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hf
  have hSub : Subsingleton (N ⧸ f.range) := by
    rw [hTop]
    exact QuotientAddGroup.subsingleton_quotient_top
  letI := hSub
  rintro ⟨e⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne P
  exact hxy (e.symm.injective (Subsingleton.elim _ _))

/-- Paper 4, p. 116, Theorem 3.23 with M=6, p=3 and k=2.
The printed difference of cyclic inclusions has trivial cokernel. -/
theorem paper4_cech_gcd_cokernel_false :
    ¬ Nonempty ((ZMod 18 ⧸ cechSixNine.range) ≃ ZMod 3) :=
  noEquivOfSurjectiveDifference cechSixNine cechSixNine_surjective

/-- Paper 4, p. 138, the stated M=6, N=10 run.
The printed difference has trivial cokernel at these exact moduli. -/
theorem paper4_cech_worked_cokernel_false :
    ¬ Nonempty ((ZMod 30 ⧸ cechSixTen.range) ≃ ZMod 2) :=
  noEquivOfSurjectiveDifference cechSixTen cechSixTen_surjective

private def paper6SignedInclusion (x : ZMod 18) : ZMod 6 × ZMod 9 :=
  (ZMod.castHom (by decide : 6 ∣ 18) (ZMod 6) x,
    -(ZMod.castHom (by decide : 9 ∣ 18) (ZMod 9) x))

private def paper6ResidueDifference (ab : ZMod 6 × ZMod 9) : ZMod 3 :=
  ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3) ab.1 -
    ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3) ab.2

/-- Paper 6, p. 220, Proposition 10.7.
The printed anti-diagonal followed by the printed difference is nonzero. -/
theorem paper6_printed_sequence_not_complex :
    ¬ ∀ x, paper6ResidueDifference (paper6SignedInclusion x) = 0 := by
  intro h
  have hOne := h 1
  simp only [paper6ResidueDifference, paper6SignedInclusion, Prod.fst_mk,
    Prod.snd_mk, map_one, map_neg] at hOne
  exact (by decide : (1 : ZMod 3) - (-1) ≠ 0) hOne

end ManuscriptAudit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.paper3_prime_two_misses_numeric_window,
    ``ManuscriptAudit.paper2_good_reduction_does_not_give_unique_point_lifts,
    ``ManuscriptAudit.coprime_principal_open_union_ne_product_open,
    ``ManuscriptAudit.paper8_printed_cusp_representative_false,
    ``ManuscriptAudit.paper8_doubling_bound_does_not_follow_from_tail_identity,
    ``ManuscriptAudit.paper4_cech_gcd_cokernel_false,
    ``ManuscriptAudit.paper4_cech_worked_cokernel_false,
    ``ManuscriptAudit.paper6_printed_sequence_not_complex] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
