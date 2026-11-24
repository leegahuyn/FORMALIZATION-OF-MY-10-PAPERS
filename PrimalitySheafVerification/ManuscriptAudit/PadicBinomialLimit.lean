import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.Tactic.NormCast
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The normalized binomial coefficients for the p-adic logarithm

For Paper 6's p-adic logarithm in §D.2, the binomial expansion of
\(((1+u)^{p^j}-1)/p^j\) has the coefficients studied here. Each
coefficient converges to its logarithmic counterpart. A summable
majorant gives the normalized power limit on the open unit ball.
The product identity for finite powers then gives logarithmic additivity.
-/

namespace ManuscriptAudit.PadicBinomialLimit

open Filter
open scoped Topology

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient of \(u^{k+1}\) in the normalized binomial expansion. -/
def normalizedBinomial (j k : ℕ) : ℚ_[p] :=
  (Nat.choose (p ^ j) (k + 1) : ℚ_[p]) / (p : ℚ_[p]) ^ j

private theorem prime_pow_pos (j : ℕ) : 0 < p ^ j :=
  pow_pos (Fact.out : p.Prime).pos j

/-- Cancel the leading factor in the binomial coefficient before
taking the limit. The identity also holds when the coefficient vanishes. -/
theorem normalizedBinomial_eq (j k : ℕ) :
    normalizedBinomial p j k =
      (Nat.choose (p ^ j - 1) k : ℚ_[p]) / ((k + 1 : ℕ) : ℚ_[p]) := by
  have hj : (p ^ j - 1) + 1 = p ^ j :=
    Nat.sub_add_cancel (prime_pow_pos p j)
  have hd : (p : ℚ_[p]) ^ j ≠ 0 :=
    pow_ne_zero j (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hk : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.succ_ne_zero
  have h := Nat.add_one_mul_choose_eq (p ^ j - 1) k
  rw [hj] at h
  unfold normalizedBinomial
  apply (div_eq_div_iff hd hk).mpr
  have hcast := congrArg (fun n : ℕ => (n : ℚ_[p])) h
  push_cast at hcast
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ = (p : ℚ_[p]) ^ j * (Nat.choose (p ^ j - 1) k : ℚ_[p]) := hcast.symm
    _ = _ := mul_comm _ _

private theorem shifted_choose_eq (j k : ℕ) :
    (Nat.choose (p ^ j - 1) k : ℚ_[p]) =
      Ring.choose ((p : ℚ_[p]) ^ j - 1) k := by
  have hcast : ((p ^ j - 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ j - 1 := by
    rw [Nat.cast_sub (prime_pow_pos p j), Nat.cast_pow, Nat.cast_one]
  rw [← hcast, Ring.choose_natCast]

private theorem continuous_ring_choose (k : ℕ) :
    Continuous (fun z : ℚ_[p] => Ring.choose z k) := by
  have he : Continuous (fun z : ℚ_[p] => (descPochhammer ℤ k).smeval z) := by
    simpa only [Polynomial.eval₂_smulOneHom_eq_smeval] using
      (descPochhammer ℤ k).continuous_eval₂ (RingHom.smulOneHom : ℤ →+* ℚ_[p])
  simp only [Ring.choose_eq_smul, smul_eq_mul]
  exact
    (continuous_const : Continuous (fun _ : ℚ_[p] => (k.factorial : ℚ_[p])⁻¹)).mul he

private theorem ring_choose_neg_one (k : ℕ) :
    Ring.choose (-1 : ℚ_[p]) k = (-1 : ℚ_[p]) ^ k := by
  rw [Ring.choose_neg', Ring.multichoose_one, Units.smul_def, zsmul_eq_mul, mul_one]
  exact Int.cast_negOnePow_natCast _ _

/-- Each normalized binomial coefficient tends to the corresponding
coefficient of the p-adic logarithm. -/
theorem tendsto_normalizedBinomial (k : ℕ) :
    Tendsto (fun j : ℕ => normalizedBinomial p j k) atTop
      (𝓝 (((-1 : ℚ_[p]) ^ k) / ((k + 1 : ℕ) : ℚ_[p]))) := by
  have hp : Tendsto (fun j : ℕ => (p : ℚ_[p]) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := p))
  have hs : Tendsto (fun j : ℕ => (p : ℚ_[p]) ^ j - 1) atTop (𝓝 (-1)) := by
    simpa only [zero_sub] using hp.sub (tendsto_const_nhds (x := (1 : ℚ_[p])))
  have hc : ContinuousAt (fun z : ℚ_[p] => Ring.choose z k) (-1) :=
    (continuous_ring_choose p k).continuousAt
  have hh := hc.tendsto.comp hs
  rw [ring_choose_neg_one p k] at hh
  convert hh.div_const (((k + 1 : ℕ) : ℚ_[p])) using 1
  funext j
  simp only [normalizedBinomial_eq, shifted_choose_eq, Function.comp_apply]

private theorem norm_inv_nat_succ_le (k : ℕ) :
    ‖((k + 1 : ℕ) : ℚ_[p])⁻¹‖ ≤ (k + 1 : ℝ) := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr k.succ_ne_zero),
    Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]
  exact_mod_cast Nat.le_of_dvd k.succ_pos (pow_padicValNat_dvd (p := p) (n := k + 1))

/-- The coefficient bound is uniform in the binomial exponent. -/
theorem norm_normalizedBinomial_le (j k : ℕ) :
    ‖normalizedBinomial p j k‖ ≤ (k + 1 : ℝ) := by
  rw [normalizedBinomial_eq, div_eq_mul_inv, norm_mul]
  have hnum : ‖(Nat.choose (p ^ j - 1) k : ℚ_[p])‖ ≤ 1 := by
    simpa only [Int.cast_natCast] using
      (Padic.norm_int_le_one (p := p) (Nat.choose (p ^ j - 1) k : ℤ))
  exact
    (mul_le_mul_of_nonneg_right hnum (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_inv_nat_succ_le p k)

/-- Uniform domination of the normalized binomial summands. -/
theorem norm_normalizedBinomial_mul_pow_le (u : ℚ_[p]) (j k : ℕ) :
    ‖normalizedBinomial p j k * u ^ (k + 1)‖ ≤
      (k + 1 : ℝ) * ‖u‖ ^ (k + 1) := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (norm_normalizedBinomial_le p j k)
    (pow_nonneg (norm_nonneg u) (k + 1))


/-- Pointwise convergence of the full summand to the logarithm term. -/
theorem tendsto_normalizedBinomial_mul_pow (u : ℚ_[p]) (k : ℕ) :
    Tendsto (fun j : ℕ => normalizedBinomial p j k * u ^ (k + 1)) atTop
      (𝓝 (((-1 : ℚ_[p]) ^ k * u ^ (k + 1)) / (k + 1 : ℚ_[p]))) := by
  simpa only [div_mul_eq_mul_div, Nat.cast_add, Nat.cast_one] using
    (tendsto_normalizedBinomial p k).mul
      (tendsto_const_nhds (x := u ^ (k + 1)))

/-- On the open unit ball the dominating real sequence is summable. -/
theorem summable_binomial_majorant {u : ℚ_[p]} (hu : ‖u‖ < 1) :
    Summable (fun k : ℕ => (k + 1 : ℝ) * ‖u‖ ^ (k + 1)) := by
  have h : Summable (fun k : ℕ => (k : ℝ) * ‖u‖ ^ k) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using hu))
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h


/-- The \(p^j\)-th finite difference of the multiplicative power map,
divided by \(p^j\). -/
def normalizedPower (u : ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  ((1 + u) ^ (p ^ j) - 1) / (p : ℚ_[p]) ^ j

/-- The p-adic logarithm series \(\sum_{k\geq 0}(-1)^k u^{k+1}/(k+1)\). -/
def padicLogSeries (u : ℚ_[p]) : ℚ_[p] :=
  ∑' k : ℕ, (-1 : ℚ_[p]) ^ k * u ^ (k + 1) / (k + 1 : ℚ_[p])

private theorem one_add_pow_sub_one (u : ℚ_[p]) (n : ℕ) :
    (1 + u) ^ n - 1 =
      ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℚ_[p]) * u ^ (k + 1) := by
  rw [add_comm 1 u, add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, add_sub_cancel_right]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The normalized binomial summands are finitely supported at each
fixed power, and their sum is the normalized power difference. -/
theorem tsum_normalizedBinomial_eq_normalizedPower (u : ℚ_[p]) (j : ℕ) :
    (∑' k : ℕ, normalizedBinomial p j k * u ^ (k + 1)) = normalizedPower p u j := by
  rw [tsum_eq_sum (s := Finset.range (p ^ j))]
  · simp only [normalizedPower, one_add_pow_sub_one, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [normalizedBinomial, div_eq_mul_inv]
    ring
  · intro k hk
    have he : p ^ j ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    simp [normalizedBinomial, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le he)]

/-- The p-adic logarithm is the limit of the normalized power
differences on its open unit ball. -/
theorem tendsto_normalizedPower {u : ℚ_[p]} (hu : ‖u‖ < 1) :
    Tendsto (normalizedPower p u) atTop (𝓝 (padicLogSeries p u)) := by
  have hlim : Tendsto (fun j : ℕ => ∑' k : ℕ, normalizedBinomial p j k * u ^ (k + 1))
      atTop (𝓝 (padicLogSeries p u)) := by
    unfold padicLogSeries
    exact tendsto_tsum_of_dominated_convergence (summable_binomial_majorant p hu)
      (tendsto_normalizedBinomial_mul_pow p u) (Filter.Eventually.of_forall
        (fun j k => norm_normalizedBinomial_mul_pow_le p u j k))
  simpa only [tsum_normalizedBinomial_eq_normalizedPower] using hlim

private theorem norm_multiplicative_argument_lt {u v : ℚ_[p]}
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) : ‖u + v + u * v‖ < 1 := by
  have huv : ‖u * v‖ < 1 := by
    rw [norm_mul]
    calc
      ‖u‖ * ‖v‖ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left hv.le (norm_nonneg _)
      _ = ‖u‖ := mul_one _
      _ < 1 := hu
  have hs : ‖u + v‖ < 1 := (Padic.nonarchimedean u v).trans_lt (max_lt hu hv)
  exact (Padic.nonarchimedean (u + v) (u * v)).trans_lt (max_lt hs huv)

private theorem normalizedPower_multiplicative_argument (u v : ℚ_[p]) (j : ℕ) :
    normalizedPower p (u + v + u * v) j =
      normalizedPower p u j + normalizedPower p v j +
        (p : ℚ_[p]) ^ j * normalizedPower p u j * normalizedPower p v j := by
  have he : 1 + (u + v + u * v) = (1 + u) * (1 + v) := by ring
  unfold normalizedPower
  rw [he, mul_pow]
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpj : (p : ℚ_[p]) ^ j ≠ 0 := pow_ne_zero j hp
  field_simp [hp, hpj] <;> ring

/-- The convergent p-adic logarithm series sends multiplication on
the principal units to addition, for every residue prime. -/
theorem padicLogSeries_additive {u v : ℚ_[p]} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    padicLogSeries p (u + v + u * v) = padicLogSeries p u + padicLogSeries p v := by
  have hL := tendsto_normalizedPower p (norm_multiplicative_argument_lt p hu hv)
  have hu' := tendsto_normalizedPower p hu
  have hv' := tendsto_normalizedPower p hv
  have hp : Tendsto (fun j : ℕ => (p : ℚ_[p]) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := p))
  have hR : Tendsto
      (fun j : ℕ => normalizedPower p u j + normalizedPower p v j +
        (p : ℚ_[p]) ^ j * normalizedPower p u j * normalizedPower p v j)
      atTop (𝓝 (padicLogSeries p u + padicLogSeries p v)) := by
    simpa only [zero_mul, add_zero] using (hu'.add hv').add ((hp.mul hu').mul hv')
  have he : normalizedPower p (u + v + u * v) =
      fun j : ℕ => normalizedPower p u j + normalizedPower p v j +
        (p : ℚ_[p]) ^ j * normalizedPower p u j * normalizedPower p v j :=
    funext (normalizedPower_multiplicative_argument p u v)
  rw [he] at hL
  exact tendsto_nhds_unique hL hR


/-- Every principal unit has norm one. -/
theorem norm_eq_one_of_principal_unit {y : ℚ_[p]} (hy : ‖y - 1‖ < 1) : ‖y‖ = 1 := by
  have hupper : ‖y‖ ≤ 1 := by
    have h := Padic.nonarchimedean (y - 1) (1 : ℚ_[p])
    simpa only [sub_add_cancel, norm_one, max_eq_right hy.le] using h
  have hlower : 1 ≤ ‖y‖ := by
    by_contra h
    have hy' : ‖y‖ < 1 := lt_of_not_ge h
    have hq := Padic.nonarchimedean y (-(y - 1))
    have he : y + -(y - 1) = (1 : ℚ_[p]) := by ring
    rw [he, norm_one, norm_neg] at hq
    exact (not_lt_of_ge hq) (max_lt hy' hy)
  exact le_antisymm hupper hlower

/-- The quotient of two principal units is a principal unit. -/
theorem norm_ratio_sub_one_lt_of_principal_units {x y : ℚ_[p]}
    (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : ‖x / y - 1‖ < 1 := by
  have hny := norm_eq_one_of_principal_unit p hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by rw [hny]; exact zero_lt_one)
  have hsub : x / y - 1 = (x - y) / y := by rw [sub_div, div_self hy0]
  have hdiff : ‖x - y‖ < 1 := by
    have h := Padic.nonarchimedean (x - 1) (-(y - 1))
    have he : x - 1 + -(y - 1) = x - y := by ring
    rw [he, norm_neg] at h
    exact h.trans_lt (max_lt hx hy)
  rw [hsub, norm_div, hny, div_one]
  exact hdiff

/-- On principal units, the difference of logarithms is the logarithm
of the quotient. -/
theorem padicLogSeries_sub_eq_ratio_of_principal_units {x y : ℚ_[p]}
    (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    padicLogSeries p (x - 1) - padicLogSeries p (y - 1) =
      padicLogSeries p (x / y - 1) := by
  have hny := norm_eq_one_of_principal_unit p hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by rw [hny]; exact zero_lt_one)
  have hratio := norm_ratio_sub_one_lt_of_principal_units p hx hy
  have he : (y - 1) + (x / y - 1) + (y - 1) * (x / y - 1) = x - 1 := by
    calc
      _ = y * (x / y) - 1 := by ring
      _ = _ := by rw [mul_comm y, div_mul_cancel₀ x hy0]
  have h := padicLogSeries_additive p hy hratio
  rw [he] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- Reduction to \(\mathbb F_p\) sends a p-adic unit to a nonzero
element, so its \((p-1)\)-st power is a principal unit. -/
theorem norm_pow_card_sub_one_sub_one_lt_of_unit {x : ℚ_[p]}
    (hx : ‖x‖ = 1) : ‖x ^ (p - 1) - 1‖ < 1 := by
  let z : ℤ_[p] := ⟨x, hx.le⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr (show ‖z‖ = 1 from hx)
  have hres : PadicInt.toZMod z ≠ 0 := (hz.map (PadicInt.toZMod (p := p))).ne_zero
  have hpow : PadicInt.toZMod z ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hres
  have hred : PadicInt.toZMod (z ^ (p - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, hpow, sub_self]
  have hmem : z ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]
    exact RingHom.mem_ker.mpr hred
  have hsmall : ‖z ^ (p - 1) - 1‖ < 1 := by
    simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using hmem
  have hzpow : ((z ^ (p - 1) : ℤ_[p]) : ℚ_[p]) = x ^ (p - 1) :=
    PadicInt.coe_pow z (p - 1)
  rw [PadicInt.norm_def, PadicInt.coe_sub, hzpow, PadicInt.coe_one] at hsmall
  exact hsmall

private theorem padicLogSeries_principal_pow {x : ℚ_[p]} (hx : ‖x - 1‖ < 1) (n : ℕ) :
    ‖x ^ n - 1‖ < 1 ∧
      padicLogSeries p (x ^ n - 1) = (n : ℚ_[p]) * padicLogSeries p (x - 1) := by
  induction n with
  | zero =>
    have hzero : padicLogSeries p 0 = 0 := by
      simp [padicLogSeries, zero_pow (Nat.succ_ne_zero _)]
    simp [hzero]
  | succ n ih =>
    obtain ⟨hn, hlog⟩ := ih
    have he : x ^ (n + 1) - 1 =
        (x ^ n - 1) + (x - 1) + (x ^ n - 1) * (x - 1) := by
      rw [pow_succ]
      ring
    constructor
    · rw [he]
      exact norm_multiplicative_argument_lt p hn hx
    · rw [he, padicLogSeries_additive p hn hx, hlog, Nat.cast_succ, add_mul, one_mul]

/-- The logarithm on p-adic units, defined through the
\((p-1)\)-st power in the principal units. -/
def padicLogUnit (x : ℚ_[p]) : ℚ_[p] :=
  padicLogSeries p (x ^ (p - 1) - 1) / ((p - 1 : ℕ) : ℚ_[p])

/-- The logarithm on units agrees with the series on principal units. -/
theorem padicLogUnit_eq_series_of_principal_unit {x : ℚ_[p]} (hx : ‖x - 1‖ < 1) :
    padicLogUnit p x = padicLogSeries p (x - 1) := by
  have hd : ((p - 1 : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
  unfold padicLogUnit
  rw [(padicLogSeries_principal_pow p hx (p - 1)).2]
  exact (div_eq_iff hd).mpr (mul_comm _ _)

/-- The difference of logarithms is the logarithm of the quotient
for all p-adic units. -/
theorem padicLogUnit_sub_eq_ratio {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    padicLogUnit p x - padicLogUnit p y = padicLogUnit p (x / y) := by
  unfold padicLogUnit
  rw [← sub_div, div_pow]
  rw [padicLogSeries_sub_eq_ratio_of_principal_units p
    (norm_pow_card_sub_one_sub_one_lt_of_unit p hx)
    (norm_pow_card_sub_one_sub_one_lt_of_unit p hy)]

/-- The logarithm of any natural power of a unit scales by that exponent. -/
theorem padicLogUnit_pow {x : ℚ_[p]} (hx : ‖x‖ = 1) (k : ℕ) :
    padicLogUnit p (x ^ k) = (k : ℚ_[p]) * padicLogUnit p x := by
  have h : (x ^ k) ^ (p - 1) - 1 = (x ^ (p - 1)) ^ k - 1 := by
    simp only [← pow_mul, mul_comm k (p - 1)]
  unfold padicLogUnit
  rw [h, (padicLogSeries_principal_pow p (norm_pow_card_sub_one_sub_one_lt_of_unit p hx) k).2,
    mul_div_assoc]

end

end ManuscriptAudit.PadicBinomialLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicBinomialLimit.normalizedBinomial_eq,
      ``ManuscriptAudit.PadicBinomialLimit.tendsto_normalizedBinomial,
      ``ManuscriptAudit.PadicBinomialLimit.norm_normalizedBinomial_le,
      ``ManuscriptAudit.PadicBinomialLimit.norm_normalizedBinomial_mul_pow_le,
      ``ManuscriptAudit.PadicBinomialLimit.tendsto_normalizedBinomial_mul_pow,
      ``ManuscriptAudit.PadicBinomialLimit.summable_binomial_majorant,
      ``ManuscriptAudit.PadicBinomialLimit.tsum_normalizedBinomial_eq_normalizedPower,
      ``ManuscriptAudit.PadicBinomialLimit.tendsto_normalizedPower,
      ``ManuscriptAudit.PadicBinomialLimit.padicLogSeries_additive,
      ``ManuscriptAudit.PadicBinomialLimit.norm_eq_one_of_principal_unit,
      ``ManuscriptAudit.PadicBinomialLimit.norm_ratio_sub_one_lt_of_principal_units,
      ``ManuscriptAudit.PadicBinomialLimit.padicLogSeries_sub_eq_ratio_of_principal_units,
      ``ManuscriptAudit.PadicBinomialLimit.norm_pow_card_sub_one_sub_one_lt_of_unit,
      ``ManuscriptAudit.PadicBinomialLimit.padicLogUnit_eq_series_of_principal_unit,
      ``ManuscriptAudit.PadicBinomialLimit.padicLogUnit_sub_eq_ratio,
      ``ManuscriptAudit.PadicBinomialLimit.padicLogUnit_pow] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
