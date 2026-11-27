import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Two polynomial coordinate systems without common roots differ by a constant if projectively equal. -/

namespace ManuscriptAudit.RationalProjectiveNormalization

open Polynomial

variable {K : Type*} [Field K] {ι : Type*}

/-- No common zero of the coordinate polynomials over the algebraic closure. -/
def RootFree (a : ι → K[X]) : Prop :=
  ∀ x : AlgebraicClosure K, (fun i => (a i).eval₂ (algebraMap K (AlgebraicClosure K)) x) ≠ 0

/-- A common polynomial divisor of a root-free vector has degree zero. -/
theorem natDegree_common_dvd_zero {a : ι → K[X]} (ha : RootFree a)
    {d : K[X]} (hd : d ≠ 0) (hDiv : ∀ i, d ∣ a i) : d.natDegree = 0 := by
  by_contra hz
  let e := algebraMap K (AlgebraicClosure K)
  have hDegree : (d.map e).degree ≠ 0 := by
    rw [degree_map_eq_of_injective e.injective, degree_eq_natDegree hd]
    exact_mod_cast hz
  obtain ⟨x, hX⟩ := IsAlgClosed.exists_root (d.map e) hDegree
  apply ha x
  funext i
  obtain ⟨q, hq⟩ := hDiv i
  change (a i).eval₂ e x = 0
  rw [← eval_map, hq, Polynomial.map_mul, eval_mul]
  exact mul_eq_zero.mpr (Or.inl hX)

/-- A nonzero rational scalar relating root-free polynomial coordinates is a nonzero constant. -/
theorem scalar_constant_of_rootfree {a b : ι → K[X]} (ha : RootFree a) (hb : RootFree b)
    {c : RatFunc K} (hc : c ≠ 0)
    (hEq : ∀ i, algebraMap K[X] (RatFunc K) (a i) =
      c * algebraMap K[X] (RatFunc K) (b i)) :
    ∃ d : K, d ≠ 0 ∧ c = RatFunc.C d := by
  let e := algebraMap K[X] (RatFunc K)
  have hRatio (i : ι) (h : b i ≠ 0) : c = e (a i) / e (b i) :=
    (eq_div_iff (RatFunc.algebraMap_ne_zero h)).mpr (hEq i).symm
  have hDenom (i : ι) : c.denom ∣ b i := by
    by_cases h : b i = 0
    · rw [h]
      exact dvd_zero _
    · exact (RatFunc.denom_dvd h).mpr ⟨a i, hRatio i h⟩
  have hNum (i : ι) : c.num ∣ a i := by
    by_cases h : a i = 0
    · rw [h]
      exact dvd_zero _
    · have h' : b i ≠ 0 := by
        intro hz
        have he : e (a i) = 0 := by simpa only [hz, map_zero, mul_zero] using hEq i
        exact RatFunc.algebraMap_ne_zero h he
      exact (RatFunc.num_dvd h).mpr ⟨b i, h', hRatio i h'⟩
  have hD := natDegree_common_dvd_zero hb c.denom_ne_zero hDenom
  have hN := natDegree_common_dvd_zero ha (RatFunc.num_ne_zero hc) hNum
  have hd : c.denom = C (c.denom.coeff 0) := eq_C_of_natDegree_eq_zero hD
  have hn : c.num = C (c.num.coeff 0) := eq_C_of_natDegree_eq_zero hN
  let t := c.num.coeff 0 / c.denom.coeff 0
  have hC : c = RatFunc.C t := by
    calc
      c = e c.num / e c.denom := c.num_div_denom.symm
      _ = RatFunc.C t := by
        change algebraMap K[X] (RatFunc K) c.num / algebraMap K[X] (RatFunc K) c.denom = _
        rw [hn, hd, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
        exact (map_div₀ RatFunc.C _ _).symm
  exact ⟨t, fun h => hc (by simpa only [h, map_zero] using hC), hC⟩

/-- Projectively equal root-free coordinates have equal component degrees. -/
theorem natDegree_eq_of_projective {a b : ι → K[X]} (ha : RootFree a) (hb : RootFree b)
    {c : RatFunc K} (hc : c ≠ 0)
    (hEq : ∀ i, algebraMap K[X] (RatFunc K) (a i) =
      c * algebraMap K[X] (RatFunc K) (b i)) (i : ι) : (a i).natDegree = (b i).natDegree := by
  obtain ⟨d, hD, hd⟩ := scalar_constant_of_rootfree ha hb hc hEq
  have h : a i = C d * b i := by
    apply RatFunc.algebraMap_injective K
    rw [map_mul, RatFunc.algebraMap_C, ← hd]
    exact hEq i
  rw [h, natDegree_C_mul hD]

/-- Projective equality after any field extension already preserves the root-free degrees. -/
theorem natDegree_eq_of_projective_extension {L : Type*} [Field L] [Algebra (RatFunc K) L]
    {a b : ι → K[X]} (ha : RootFree a) (hb : RootFree b)
    {c : L} (hc : c ≠ 0)
    (hEq : ∀ i, algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) (a i)) =
      c * algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) (b i)))
    (i : ι) : (a i).natDegree = (b i).natDegree := by
  have hB : ∃ j, b j ≠ 0 := by
    by_contra! h
    apply hb 0
    funext j
    simp [h j]
  obtain ⟨j, hj⟩ := hB
  let e := algebraMap (RatFunc K) L
  let m := algebraMap K[X] (RatFunc K)
  let d : RatFunc K := m (a j) / m (b j)
  have hN : e (m (b j)) ≠ 0 := (map_ne_zero e).mpr (RatFunc.algebraMap_ne_zero hj)
  have hD : e d = c := by
    change e (m (a j) / m (b j)) = c
    rw [map_div₀, div_eq_iff hN]
    exact hEq j
  have hD₀ : d ≠ 0 := by
    intro h
    exact hc (by simpa only [h, map_zero] using hD.symm)
  refine natDegree_eq_of_projective ha hb hD₀ (fun j => e.injective ?_) i
  rw [map_mul, hD]
  exact hEq j

end ManuscriptAudit.RationalProjectiveNormalization

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RationalProjectiveNormalization.natDegree_common_dvd_zero,
      ``ManuscriptAudit.RationalProjectiveNormalization.scalar_constant_of_rootfree,
      ``ManuscriptAudit.RationalProjectiveNormalization.natDegree_eq_of_projective,
      ``ManuscriptAudit.RationalProjectiveNormalization.natDegree_eq_of_projective_extension] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
