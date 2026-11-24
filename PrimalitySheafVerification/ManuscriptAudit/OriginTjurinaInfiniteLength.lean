import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.FractionRing
import PrimalitySheafVerification.ManuscriptAudit.OriginMonomialLength

/-!
# Infinite local Tjurina length in the two vanishing-partial case

If both positive exponents vanish in the prime field, the actual Tjurina
quotient at the origin has infinite length. A branch of the equation over
the algebraic closure embeds the powers of the first coordinate into a
fraction field.
-/

namespace ManuscriptAudit.OriginTjurinaInfiniteLength

open MvPolynomial OriginMonomialLength

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

private abbrev K := ZMod p
private abbrev Plane := MvPolynomial (Fin 2) (K p)
private abbrev E := AlgebraicClosure (K p)
private abbrev P := Polynomial (E p)
private abbrev F := FractionRing (P p)

private def localIdeal (a b : ℕ) : Ideal (OriginRing (K p)) :=
  (benchmarkJacobian (K p) a b).map (algebraMap (Plane p) (OriginRing (K p)))

private abbrev Tjurina (a b : ℕ) := OriginRing (K p) ⧸ localIdeal p a b

/-- When both exponent coefficients vanish, only the equation remains
among the Tjurina generators. -/
theorem benchmarkJacobian_eq_equation (a b : ℕ) (ha : (a : K p) = 0) (hb : (b : K p) = 0) :
    benchmarkJacobian (K p) a b = Ideal.span {benchmark (K p) a b} := by
  have hA : (a : Plane p) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (MvPolynomial.C : K p →+* Plane p) ha
  have hB : (b : Plane p) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (MvPolynomial.C : K p →+* Plane p) hb
  have hder (i : Fin 2) : pderiv i (benchmark (K p) a b) = 0 := by
    simp only [benchmark, map_add, pderiv_pow, hA, hB, zero_mul, add_zero]
  unfold benchmarkJacobian
  rw [hder 0, hder 1]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact Ideal.subset_span (Set.mem_singleton _)
    · have hzero : f = 0 := by simpa using hf
      rw [hzero]
      exact Ideal.zero_mem _
  · exact Ideal.span_mono (by simp)

private def branchValues (a b : ℕ) (ζ : E p) (i : Fin 2) : P p :=
  if i = 0 then (Polynomial.X : P p) ^ b
  else Polynomial.C ζ * (Polynomial.X : P p) ^ a

private def branch (a b : ℕ) (ζ : E p) : Plane p →+* P p :=
  (MvPolynomial.aeval (branchValues p a b ζ)).toRingHom

private theorem branch_benchmark (a b : ℕ) (ζ : E p) (hζ : ζ ^ b = -1) :
    branch p a b ζ (benchmark (K p) a b) = 0 := by
  rw [benchmark, map_add, map_pow, map_pow]
  change (MvPolynomial.aeval (branchValues p a b ζ) (MvPolynomial.X 0 : Plane p)) ^ a +
    (MvPolynomial.aeval (branchValues p a b ζ) (MvPolynomial.X 1 : Plane p)) ^ b = 0
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [branchValues, eq_self, if_true, if_neg h10, mul_pow, ← map_pow, hζ, map_neg,
    map_one, neg_one_mul, ← pow_mul]
  rw [Nat.mul_comm b a, add_neg_cancel]

private theorem branch_origin (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ζ : E p)
    (f : Plane p) : (branch p a b ζ f).eval 0 =
      algebraMap (K p) (E p) (constantCoeff f) := by
  have h :
      (Polynomial.evalRingHom (0 : E p)).comp (branch p a b ζ) =
        (algebraMap (K p) (E p)).comp (constantCoeff : Plane p →+* K p) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change (MvPolynomial.aeval (branchValues p a b ζ) (MvPolynomial.C c : Plane p)).eval 0 =
        algebraMap (K p) (E p) (constantCoeff (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C,
        Polynomial.algebraMap_apply, Polynomial.eval_C]
    · intro i
      change (MvPolynomial.aeval (branchValues p a b ζ) (MvPolynomial.X i : Plane p)).eval 0 =
        algebraMap (K p) (E p) (constantCoeff (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X, map_zero]
      fin_cases i <;>
        simp [branchValues, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          zero_pow ha.ne', zero_pow hb.ne']
  exact RingHom.congr_fun h f

private def branchFraction (a b : ℕ) (ζ : E p) : Plane p →+* F p :=
  (algebraMap (P p) (F p)).comp (branch p a b ζ)

private theorem branchFraction_unit (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ζ : E p)
    (s : (originIdeal (K p)).primeCompl) :
    IsUnit (branchFraction p a b ζ s) := by
  apply isUnit_iff_ne_zero.mpr
  intro hs
  have hsP : branch p a b ζ s = 0 := by
    apply IsFractionRing.injective (P p) (F p)
    simpa only [branchFraction, RingHom.comp_apply, map_zero] using hs
  apply (show (s : Plane p) ∉ originIdeal (K p) from s.property)
  change constantCoeff (s : Plane p) = 0
  have hz := branch_origin p a b ha hb ζ (s : Plane p)
  rw [hsP, Polynomial.eval_zero] at hz
  apply (algebraMap (K p) (E p)).injective
  rw [map_zero]
  exact hz.symm

private def localBranch (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ζ : E p) :
    OriginRing (K p) →+* F p :=
  IsLocalization.lift (M := (originIdeal (K p)).primeCompl)
    (branchFraction_unit p a b ha hb ζ)

private theorem localBranch_map (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (ζ : E p)
    (s : Plane p) :
    localBranch p a b ha hb ζ (algebraMap (Plane p) (OriginRing (K p)) s) =
      branchFraction p a b ζ s :=
  IsLocalization.lift_eq (branchFraction_unit p a b ha hb ζ) s

private def quotientBranch (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (a : K p) = 0) (hB : (b : K p) = 0) (ζ : E p) (hζ : ζ ^ b = -1) :
    Tjurina p a b →+* F p := by
  let g := localBranch p a b ha hb ζ
  have hKer : localIdeal p a b ≤ RingHom.ker g := by
    unfold localIdeal
    apply Ideal.map_le_iff_le_comap.mpr
    rw [benchmarkJacobian_eq_equation p a b hA hB]
    apply Ideal.span_le.mpr
    intro s hs
    rcases Set.mem_singleton_iff.mp hs with rfl
    change g (algebraMap (Plane p) (OriginRing (K p)) (benchmark (K p) a b)) = 0
    rw [localBranch_map, branchFraction, RingHom.comp_apply, branch_benchmark p a b ζ hζ,
      map_zero]
  exact Ideal.Quotient.lift (localIdeal p a b) g (fun s hs => hKer hs)

private def localX : OriginRing (K p) :=
  algebraMap (Plane p) (OriginRing (K p)) (MvPolynomial.X 0)

private def x (a b : ℕ) : Tjurina p a b :=
  Ideal.Quotient.mk (localIdeal p a b) (localX p)

private theorem quotientBranch_x (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (a : K p) = 0) (hB : (b : K p) = 0) (ζ : E p) (hζ : ζ ^ b = -1) :
    quotientBranch p a b ha hb hA hB ζ hζ (x p a b) =
      algebraMap (P p) (F p) ((Polynomial.X : P p) ^ b) := by
  change localBranch p a b ha hb ζ
    (algebraMap (Plane p) (OriginRing (K p)) (MvPolynomial.X 0)) = _
  rw [localBranch_map]
  change algebraMap (P p) (F p)
    (MvPolynomial.aeval (branchValues p a b ζ) (MvPolynomial.X 0 : Plane p)) = _
  rw [MvPolynomial.aeval_X]
  simp [branchValues]

private theorem powers_x_injective (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (a : K p) = 0) (hB : (b : K p) = 0) :
    Function.Injective (fun n : ℕ => (x p a b) ^ n) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : E p) hb
  intro n m h
  have hF := congrArg (quotientBranch p a b ha hb hA hB ζ hζ) h
  simp only [map_pow, quotientBranch_x] at hF
  have hP : ((Polynomial.X : P p) ^ b) ^ n = ((Polynomial.X : P p) ^ b) ^ m := by
    apply IsFractionRing.injective (P p) (F p)
    simpa only [map_pow] using hF
  have hDeg : b * n = b * m := by
    simpa only [← pow_mul, Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree hP
  exact Nat.eq_of_mul_eq_mul_left hb hDeg

/-- The actual quotient, after localization at the origin, has infinite
length as a vector space over the prime field. -/
theorem benchmarkTjurina_field_length_eq_top (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (a : K p) = 0) (hB : (b : K p) = 0) :
    Module.length (K p) (Tjurina p a b) = ⊤ := by
  by_contra hlen
  have hfin := Module.length_ne_top_iff.mp hlen
  letI : IsNoetherian (K p) (Tjurina p a b) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  letI : Infinite (Tjurina p a b) :=
    Infinite.of_injective _ (powers_x_injective p a b ha hb hA hB)
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite (Tjurina p a b) := Module.finite_of_finite (K p)
  exact not_finite (Tjurina p a b)

private theorem localX_mem_maximal :
    localX p ∈ IsLocalRing.maximalIdeal (OriginRing (K p)) := by
  rw [localX, ← Localization.AtPrime.map_eq_maximalIdeal (I := originIdeal (K p))]
  apply Ideal.mem_map_of_mem (algebraMap (Plane p) (OriginRing (K p)))
  change constantCoeff (MvPolynomial.X (0 : Fin 2) : Plane p) = 0
  exact MvPolynomial.constantCoeff_X (R := K p) (0 : Fin 2)

set_option backward.isDefEq.respectTransparency true in
private theorem quotient_length_eq_top_of_nonnilpotent {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [Nontrivial (A ⧸ I)] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hn : ¬ IsNilpotent (Ideal.Quotient.mk I t)) : Module.length A (A ⧸ I) = ⊤ := by
  let Q := A ⧸ I
  let q : A →+* Q := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  letI : IsLocalRing Q := IsLocalRing.of_surjective' q hq
  letI : IsLocalHom q := IsLocalHom.of_surjective q hq
  have hx : q t ∈ IsLocalRing.maximalIdeal Q :=
    (IsLocalRing.map_maximalIdeal_le q) (Ideal.mem_map_of_mem q ht)
  calc
    _ = Module.length Q Q :=
      Module.length_eq_of_surjective (S := A) (R := Q) (M := Q)
        (show Function.Surjective (algebraMap A Q) from hq)
    _ = ⊤ := by
      by_contra hlen
      have hf := Module.length_ne_top_iff.mp hlen
      letI : IsArtinianRing Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hf).2
      obtain ⟨n, hJ⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Q)
      have hj : q t ∈ Ideal.jacobson (⊥ : Ideal Q) :=
        IsLocalRing.maximalIdeal_le_jacobson _ hx
      have hp := Ideal.pow_mem_pow hj n
      rw [hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
      exact hn ⟨n, hp⟩

/-- The same quotient has infinite length as a module over the actual
ambient local ring at the origin. -/
theorem benchmarkTjurina_local_length_eq_top (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (a : K p) = 0) (hB : (b : K p) = 0) :
    Module.length (OriginRing (K p)) (Tjurina p a b) = ⊤ := by
  letI : Infinite (Tjurina p a b) :=
    Infinite.of_injective _ (powers_x_injective p a b ha hb hA hB)
  have hn : ¬ IsNilpotent (x p a b) := by
    rintro ⟨n, hn⟩
    have hs : (x p a b) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
    exact Nat.succ_ne_self n (powers_x_injective p a b ha hb hA hB (hs.trans hn.symm))
  exact quotient_length_eq_top_of_nonnilpotent (localIdeal p a b) (localX p)
    (localX_mem_maximal p) hn

end

end ManuscriptAudit.OriginTjurinaInfiniteLength

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.OriginTjurinaInfiniteLength.benchmarkJacobian_eq_equation,
    ``ManuscriptAudit.OriginTjurinaInfiniteLength.benchmarkTjurina_field_length_eq_top,
    ``ManuscriptAudit.OriginTjurinaInfiniteLength.benchmarkTjurina_local_length_eq_top] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
