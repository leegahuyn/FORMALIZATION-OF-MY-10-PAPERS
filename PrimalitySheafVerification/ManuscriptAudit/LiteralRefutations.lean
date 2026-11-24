import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open scoped BigOperators

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
      simpa [show |(2 : ℝ) - 1| = 1 by norm_num] using hdiv
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
  change cyclicInclusion 6 3 (by decide) (x : ZMod 6) -
    cyclicInclusion 9 2 (by decide) (x : ZMod 9) = (x : ZMod 18)
  rw [cyclicInclusion_int, cyclicInclusion_int]
  ring

private theorem cechSixTen_surjective : Function.Surjective cechSixTen := by
  intro r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := 30) r
  refine ⟨(((2 * x : ℤ) : ZMod 6), ((3 * x : ℤ) : ZMod 10)), ?_⟩
  change cyclicInclusion 6 5 (by decide) ((2 * x : ℤ) : ZMod 6) -
    cyclicInclusion 10 3 (by decide) ((3 * x : ℤ) : ZMod 10) = (x : ZMod 30)
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
  simp only [paper6ResidueDifference, paper6SignedInclusion,
    map_one, map_neg] at hOne
  exact (by decide : (1 : ZMod 3) - (-1) ≠ 0) hOne


/-- Paper 6, pp. 190–191. Subtraction of integer representatives does not
define the displayed map to the quotient by the lcm. -/
theorem paper6_lcm_difference_cannot_descend :
    ¬ ∃ δ : ZMod 6 × ZMod 9 → ZMod 18,
      ∀ a b : ℤ,
        δ ((a : ZMod 6), (b : ZMod 9)) = ((a - b : ℤ) : ZMod 18) := by
  rintro ⟨δ, hδ⟩
  have hzero : δ (0, 0) = 0 := by simpa using hδ 0 0
  have hsixMod : ((6 : ℤ) : ZMod 6) = 0 := by decide
  have hsix : δ (0, 0) = ((6 : ℤ) : ZMod 18) := by
    simpa only [sub_zero, Int.cast_zero, hsixMod] using hδ 6 0
  exact (by decide : (0 : ZMod 18) ≠ ((6 : ℤ) : ZMod 18))
    (hzero.symm.trans hsix)

private def hasseExampleCount : ℕ :=
  1 + ((Finset.univ : Finset (ZMod 7 × ZMod 7)).filter
    (fun xy => xy.2 ^ 2 = xy.1 ^ 3 - 7 * xy.1 + 3)).card

private def hasseExampleTrace : ℤ := 7 + 1 - (hasseExampleCount : ℤ)

/-- Paper 5, p. 161. The Hasse scanner uses 2 times the integer
square root. Its conclusion fails for a valid curve in its own family. -/
theorem paper5_integer_hasse_threshold_false :
    (16 * (4 * (7 : ZMod 7) ^ 3 - 27 * 3 ^ 2) ≠ 0) ∧
      hasseExampleCount = 13 ∧ hasseExampleTrace = -5 ∧
      hasseExampleTrace ^ 2 ≤ 4 * (7 : ℤ) ∧
      ¬ hasseExampleTrace.natAbs ≤ 2 * Nat.sqrt 7 := by
  have hSqrt : Nat.sqrt 7 = 2 := Nat.sqrt_add_eq' 2 (by decide : 3 ≤ 2 + 2)
  rw [hSqrt]
  decide

private def printedCoefficientExponent : Fin 11 → ℚ :=
  ![(-1715 : ℚ) / 2, -3483 / 4, -1711 / 2, -3477 / 4,
    -1709 / 2, -3475 / 4, -1709 / 2, -3477 / 4,
    -1711 / 2, -3483 / 4, -1715 / 2]

/-- Paper 8, p. 310, Table 1. If a row extracts the coefficient of its
printed exponent, the displayed e₁ target is impossible. -/
theorem paper8_printed_coefficient_rows_cannot_realize_first_target
    (coeff : ℚ → Fin 22 → ℚ) :
    ¬ ∃ x : Fin 22 → ℚ, ∀ i : Fin 11,
      (∑ j : Fin 22, coeff (printedCoefficientExponent i) j * x j) =
        (if i = 0 then 1 else 0) := by
  rintro ⟨x, hx⟩
  have hFirst := hx 0
  have hLast := hx 10
  have hRows : printedCoefficientExponent 0 = printedCoefficientExponent 10 := by rfl
  rw [if_pos rfl, hRows] at hFirst
  rw [if_neg (by decide : (10 : Fin 11) ≠ 0)] at hLast
  exact one_ne_zero (hFirst.symm.trans hLast)

private abbrev ComplexMatrixTwo := Matrix (Fin 2) (Fin 2) ℂ

/-- Paper 10, p. 465. Positivity and invariance under every invertible
conjugation are incompatible on the underlying real Lie algebra of GL₂(ℂ). -/
theorem paper10_no_positive_ad_invariant_gl2_form
    (B : ComplexMatrixTwo →ₗ[ℝ] ComplexMatrixTwo →ₗ[ℝ] ℝ)
    (hPos : ∀ X : ComplexMatrixTwo, X ≠ 0 → 0 < B X X)
    (hInv : ∀ G Gi X Y : ComplexMatrixTwo, G * Gi = 1 → Gi * G = 1 →
      B (Gi * X * G) (Gi * Y * G) = B X Y) : False := by
  let G : ComplexMatrixTwo := !![(1 : ℂ), 0; 0, 2]
  let Gi : ComplexMatrixTwo := !![(1 : ℂ), 0; 0, 1 / 2]
  let X : ComplexMatrixTwo := !![(0 : ℂ), 1; 0, 0]
  have hG : G * Gi = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Gi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hGi : Gi * G = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Gi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hX : X ≠ 0 := by
    intro h
    have hEntry := congrArg (fun A : ComplexMatrixTwo => A 0 1) h
    norm_num [X] at hEntry
  have hConj : Gi * X * G = X + X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Gi, X, Matrix.mul_apply, Fin.sum_univ_two]
  have hEq := hInv G Gi X X hG hGi
  simp only [hConj, map_add, LinearMap.add_apply] at hEq
  linarith [hPos X hX]

/-- With a nonzero normalized tail, the printed plus-sign expansion and
the printed sign of the linearization in Paper 1, p. 7, are incompatible. -/
theorem paper1_printed_expansion_forces_negative_discrepancy
    (X Y T : ℚ) (hY : Y ≠ 0) (hT : T ≠ 0) (hExp : Y = X + T) :
    (X - Y) / Y ≠ T / Y := by
  intro h
  have hDiff : X - Y = T := by
    apply mul_right_cancel₀ (inv_ne_zero hY)
    simpa only [div_eq_mul_inv] using h
  exact hT (by linarith)

/-- The module support of an ideal containing a nonzero element of a
domain is the whole prime spectrum. -/
theorem support_of_ideal_with_nonzero_element
    {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) {a : R}
    (ha : a ∈ I) (ha₀ : a ≠ 0) :
    Module.support R I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rw [Module.mem_support_iff']
  refine ⟨⟨a, ha⟩, ?_⟩
  intro r hr h
  have hProduct : r * a = 0 := congrArg Subtype.val h
  have hr₀ : r = 0 := (mul_eq_zero.mp hProduct).resolve_right ha₀
  rw [hr₀] at hr
  exact hr p.asIdeal.zero_mem

/-- Papers 1 and 6. Coprime moduli 2 and 3 give a nonzero equalizer ideal
with full support, whereas the closed set V(gcd(2,3)) is empty. -/
theorem paper1_coprime_kernel_support_ne_gcd_support :
    Module.support ℤ ↥(Ideal.span {(2 : ℤ)} ⊓ Ideal.span {(3 : ℤ)} : Ideal ℤ) ≠
      PrimeSpectrum.zeroLocus ({(Nat.gcd 2 3 : ℤ)} : Set ℤ) := by
  have hSix : (6 : ℤ) ∈ Ideal.span {(2 : ℤ)} ⊓ Ideal.span {(3 : ℤ)} := by
    change 6 ∈ Ideal.span {(2 : ℤ)} ∧ 6 ∈ Ideal.span {(3 : ℤ)}
    simp only [Ideal.mem_span_singleton]
    norm_num
  rw [support_of_ideal_with_nonzero_element _ hSix (by norm_num)]
  intro h
  let p : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : p ∈ PrimeSpectrum.zeroLocus ({(Nat.gcd 2 3 : ℤ)} : Set ℤ) := by
    rw [← h]
    exact Set.mem_univ _
  have hOne : (1 : ℤ) ∈ p.asIdeal := by
    apply (PrimeSpectrum.mem_zeroLocus p _).mp hp
    change (1 : ℤ) = ((Nat.gcd 2 3 : ℕ) : ℤ)
    decide
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hOne)

/-- Paper 1, p. 17. In the case M=p=3 and k=1, the Tor term is Z/3.
It cannot inject additively into the printed integral intersection ideal. -/
theorem paper1_no_additive_injection_to_integral_intersection
    (f : ZMod 3 →+ ↥(Ideal.span {(3 : ℤ)} ⊓ Ideal.span {(3 : ℤ)} : Ideal ℤ)) :
    ¬ Function.Injective f := by
  intro hf
  have hZero : 3 • (1 : ZMod 3) = 0 := by decide
  have h := map_nsmul f 3 (1 : ZMod 3)
  rw [hZero, map_zero] at h
  have hInt : (0 : ℤ) = 3 * (f 1 : ℤ) := by
    have h' : (0 : ℤ) = 3 • (f 1 : ℤ) := congrArg Subtype.val h
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h'
  have hVal : (f 1 : ℤ) = 0 :=
    (mul_eq_zero.mp hInt.symm).resolve_left (by norm_num)
  have hMap : f 1 = 0 := Subtype.ext hVal
  have hOne : (1 : ZMod 3) = 0 := hf (hMap.trans (map_zero f).symm)
  exact (by decide : (1 : ZMod 3) ≠ 0) hOne

private abbrev pIdealThree : Ideal ℤ := Ideal.span {(3 : ℤ)}

private instance : pIdealThree.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr
    (Nat.prime_iff_prime_int.mp Nat.prime_three)

private abbrev ZAtThree := Localization.AtPrime pIdealThree

/-- Papers 1, 4, 6 and 7. At M=1, p=3 and k=1 the localization of the
intersection is proper. The printed minimum exponent gives the unit ideal. -/
theorem localized_intersection_ne_printed_minimum :
    Ideal.map (algebraMap ℤ ZAtThree)
        (Ideal.span {(1 : ℤ)} ⊓ pIdealThree) ≠
      Ideal.span {(1 : ZAtThree)} := by
  simp only [Ideal.span_singleton_one, top_inf_eq]
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact (IsLocalRing.maximalIdeal.isMaximal ZAtThree).ne_top

/-- Paper 1, p. 10, Proposition 2.5. At p=p₂=3, n=t=2 and σ=3,
the required choice y≡±1 modulo 3 conflicts with y≡0 modulo 3. -/
theorem paper1_optional_congruence_requires_compatibility :
    ¬ ∃ y : ℤ, (((y : ZMod 3) = 1) ∨ ((y : ZMod 3) = -1)) ∧
      (y : ZMod 3) = 0 := by
  rintro ⟨y, hy, hZero⟩
  rw [hZero] at hy
  exact (by decide : ¬ ((0 : ZMod 3) = 1 ∨ (0 : ZMod 3) = -1)) hy

open Polynomial in
private noncomputable def residuePolynomial3 : Polynomial (ZMod 3) := X ^ 2 + C 1

open Polynomial in
/-- Paper 2, pp. 29–30, Theorem 2.1. This non-squarefree polynomial
has no residue-field root, hence no common residue-field root with its derivative. -/
theorem paper2_repeated_geometric_root_without_rational_root :
    ¬ Squarefree (residuePolynomial3 ^ 2) ∧
      ¬ ∃ a : ZMod 3, (residuePolynomial3 ^ 2).eval a = 0 ∧
        (residuePolynomial3 ^ 2).derivative.eval a = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have hDiv : residuePolynomial3 * residuePolynomial3 ∣ residuePolynomial3 ^ 2 :=
      ⟨1, (pow_two _).trans (mul_one _).symm⟩
    have hUnit := h residuePolynomial3 hDiv
    have hDegree := Polynomial.natDegree_eq_zero_of_isUnit hUnit
    rw [residuePolynomial3, Polynomial.natDegree_X_pow_add_C] at hDegree
    exact (by decide : (2 : ℕ) ≠ 0) hDegree
  · rintro ⟨a, hRoot, _⟩
    have hNoRoot : ∀ x : ZMod 3, (x ^ 2 + 1) ^ 2 ≠ 0 := by decide
    exact hNoRoot a (by simpa [residuePolynomial3] using hRoot)

/-- Paper 3, p. 76, Lemma C. Multiplication by 3 on Z/3 has 1
in its kernel. The printed formula for the generator gives 0. -/
theorem paper3_prime_power_printed_generator_misses_kernel :
    (1 : ZMod 3) ∈ (AddMonoidHom.mulLeft (3 : ZMod 3)).ker ∧
      ((3 / (3 ^ (1 - 1)) : ℕ) : ZMod 3) = 0 ∧
      ¬ ∃ z : ℤ, z • (((3 / (3 ^ (1 - 1)) : ℕ) : ZMod 3)) = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨z, hz⟩
  rw [show ((3 / (3 ^ (1 - 1)) : ℕ) : ZMod 3) = 0 by decide, smul_zero] at hz
  exact (by decide : (0 : ZMod 3) ≠ 1) hz

/-- Paper 4, p. 107, Lemma 3.13. The free abelian group on the terminal
set is nontrivial. Free abelianization does not preserve the empty limit. -/
theorem paper4_free_abelianization_fails_terminal_object :
    ¬ Subsingleton (FreeAbelianGroup PUnit) := by
  intro h
  exact FreeAbelianGroup.of_ne_zero PUnit.unit (h.elim _ 0)

/-- Paper 7, pp. 253–255. The rank-one Koszul differential given by
multiplication by 3 is injective over ℤ localized at (3). Its base change
to the actual residue field has nonzero kernel because 3 maps to zero. -/
theorem paper7_rank_one_koszul_injectivity_fails_after_reduction :
    Function.Injective (fun x : ZAtThree => (3 : ZAtThree) * x) ∧
      ¬ Function.Injective (fun x : IsLocalRing.ResidueField ZAtThree =>
        IsLocalRing.residue ZAtThree 3 * x) := by
  have hThree : (3 : ZAtThree) ≠ 0 := by
    have hMap : Function.Injective (algebraMap ℤ ZAtThree) :=
      (faithfulSMul_iff_algebraMap_injective ℤ ZAtThree).mp inferInstance
    simpa only [map_ofNat, map_zero] using hMap.ne (by decide : (3 : ℤ) ≠ 0)
  have hMax : (3 : ZAtThree) ∈ IsLocalRing.maximalIdeal ZAtThree := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← map_ofNat (algebraMap ℤ ZAtThree) 3]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hRes : IsLocalRing.residue ZAtThree 3 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hMax
  letI : IsDomain ZAtThree := IsLocalization.isDomain_of_local_atPrime inferInstance
  refine ⟨fun _ _ h => mul_left_cancel₀ hThree h, ?_⟩
  intro hInj
  have hEq : (0 : IsLocalRing.ResidueField ZAtThree) = 1 := hInj (by simp [hRes])
  exact zero_ne_one hEq

/-- Paper 1, p. 17, Example 4.5. This finite computation uses Lean's
kernel reduction for the actual multiplication map on ZMod 9. -/
theorem paper1_worked_tor_kernel_count :
    Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by
  decide


/-- The reverse Hensel implication without a separate derivative
hypothesis fails at every prime. The root of X² above residue zero is unique. -/
theorem unique_padic_residue_lift_does_not_imply_unit_derivative
    (p : ℕ) [Fact (Nat.Prime p)] :
    (∃! z : ℤ_[p], ((Polynomial.X : Polynomial ℤ_[p]) ^ 2).eval z = 0 ∧
      PadicInt.toZMod (p := p) z = 0) ∧
    ¬ IsUnit (((Polynomial.X : Polynomial ℤ_[p]) ^ 2).derivative.eval 0) := by
  refine ⟨⟨0, ⟨by simp, map_zero _⟩, ?_⟩, ?_⟩
  · rintro z ⟨hz, _⟩
    have hz' : z ^ 2 = 0 := by simpa using hz
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz'
  · simp

/-- Paper 4, p. 99. With M=6 and p=3 the two printed principal
opens both omit the prime (3), so they do not cover Spec ℤ. -/
theorem paper4_shared_prime_opens_do_not_cover :
    PrimeSpectrum.basicOpen (6 : ℤ) ⊔ PrimeSpectrum.basicOpen 3 ≠ ⊤ := by
  let p : PrimeSpectrum ℤ := ⟨pIdealThree, inferInstance⟩
  have hSix : p ∉ PrimeSpectrum.basicOpen (6 : ℤ) := by
    rw [PrimeSpectrum.mem_basicOpen]
    change ¬ ((6 : ℤ) ∉ pIdealThree)
    exact fun h => h (Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩)
  have hThree : p ∉ PrimeSpectrum.basicOpen (3 : ℤ) := by
    rw [PrimeSpectrum.mem_basicOpen]
    change ¬ ((3 : ℤ) ∉ pIdealThree)
    exact fun h => h (Ideal.mem_span_singleton_self _)
  intro h
  have hp : p ∈ PrimeSpectrum.basicOpen (6 : ℤ) ⊔ PrimeSpectrum.basicOpen 3 := by
    rw [h]
    trivial
  change p ∈ PrimeSpectrum.basicOpen (6 : ℤ) ∨ p ∈ PrimeSpectrum.basicOpen 3 at hp
  exact hp.elim hSix hThree

/-- Paper 3, p. 81. A single local exponent at q=3 contributes one
to the unweighted count and log(3) to the information expression. -/
theorem paper3_ic_log_two_scaling_not_equality :
    Real.log (3 : ℝ) / Real.log 2 ≠ 1 := by
  have hPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hStrict : Real.log (2 : ℝ) < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  intro hEq
  have h := (div_eq_iff (ne_of_gt hPos)).mp hEq
  rw [one_mul] at h
  exact (ne_of_gt hStrict) h

/-- Paper 1, p. 10, Proposition 2.4. At p=p₂=3, n=2, A=4
and y=2, the printed indexed-prime modulus has order two although t=1. -/
theorem paper1_indexed_prime_modulus_can_exceed_printed_order :
    padicValNat 3 (4 - 1) = 1 ∧ padicValNat 3 (3 * 2 + (4 - 1)) = 2 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨padicValNat_self, ?_⟩
  change padicValNat 3 (3 ^ 2) = 2
  rw [padicValNat.pow, padicValNat_self] <;> decide

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
    ``ManuscriptAudit.paper6_printed_sequence_not_complex,
    ``ManuscriptAudit.paper6_lcm_difference_cannot_descend,
    ``ManuscriptAudit.paper5_integer_hasse_threshold_false,
    ``ManuscriptAudit.paper8_printed_coefficient_rows_cannot_realize_first_target,
    ``ManuscriptAudit.paper10_no_positive_ad_invariant_gl2_form,
    ``ManuscriptAudit.paper1_printed_expansion_forces_negative_discrepancy,
    ``ManuscriptAudit.support_of_ideal_with_nonzero_element,
    ``ManuscriptAudit.paper1_coprime_kernel_support_ne_gcd_support,
    ``ManuscriptAudit.paper1_no_additive_injection_to_integral_intersection,
    ``ManuscriptAudit.localized_intersection_ne_printed_minimum,
    ``ManuscriptAudit.paper1_optional_congruence_requires_compatibility,
    ``ManuscriptAudit.paper2_repeated_geometric_root_without_rational_root,
    ``ManuscriptAudit.paper3_prime_power_printed_generator_misses_kernel,
    ``ManuscriptAudit.paper4_free_abelianization_fails_terminal_object,
    ``ManuscriptAudit.paper7_rank_one_koszul_injectivity_fails_after_reduction,
    ``ManuscriptAudit.paper1_worked_tor_kernel_count,
    ``ManuscriptAudit.unique_padic_residue_lift_does_not_imply_unit_derivative,
    ``ManuscriptAudit.paper4_shared_prime_opens_do_not_cover,
    ``ManuscriptAudit.paper3_ic_log_two_scaling_not_equality,
    ``ManuscriptAudit.paper1_indexed_prime_modulus_can_exceed_printed_order] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
