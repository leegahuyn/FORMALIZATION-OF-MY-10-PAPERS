import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper4DirichletDensity

/-! The Dirichlet density after removal of a literal finite support is a
limit of the corresponding series over precisely the remaining primes. -/

namespace ManuscriptAudit.Paper4PrimeDirichletExceptions

open Filter Topology
open scoped BigOperators
open Paper4PrimeDirichletDerivative (countCoeff primeDirichletSeries primeTerm_summable series_eq_tsum)
open FiniteSupportDirichletLimit (normalizer finiteWeight)

noncomputable section

variable {q : ℕ} [NeZero q] (a : ZMod q) (E : Finset ℕ)

private abbrev term (s : ℝ) (n : ℕ) : ℝ := countCoeff a n / (n : ℝ) ^ s

private def inside (s : ℝ) (n : ℕ) : ℝ := if n ∈ E then term a s n else 0

def afterExceptionsSeries (s : ℝ) : ℝ :=
  ∑' n, if n ∈ E then 0 else term a s n

private theorem inside_summable (s : ℝ) : Summable (inside a E s) := by
  apply summable_of_hasFiniteSupport
  apply E.finite_toSet.subset
  intro n hn
  change n ∈ E
  by_contra h
  exact hn (by simp [inside, h])

private theorem inside_sum (s : ℝ) :
    (∑' n, inside a E s n) = finiteWeight (E.filter (fun n ↦ n.Prime ∧ (n : ZMod q) = a)) s := by
  rw [tsum_eq_sum (s := E) (by intro n hn; simp [inside, hn])]
  unfold finiteWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime ∧ (n : ZMod q) = a
  · simp [inside, term, hn, hp, countCoeff, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  · simp [inside, term, hn, hp, countCoeff]

theorem afterExceptionsSeries_eq_sub {s : ℝ} (hs : 1 < s) :
    afterExceptionsSeries a E s = primeDirichletSeries a s -
      finiteWeight (E.filter (fun n ↦ n.Prime ∧ (n : ZMod q) = a)) s := by
  calc
    _ = ∑' n, term a s n - inside a E s n := by
      unfold afterExceptionsSeries
      apply tsum_congr
      intro n
      by_cases h : n ∈ E <;> simp [inside, h]
    _ = _ := by
      rw [(primeTerm_summable a hs).tsum_sub (inside_summable a E s),
        ← series_eq_tsum a hs, inside_sum a E s]

/-- Genuine remaining-prime limit, with a reduction to the literal aggregate sum. -/
theorem normalized_afterExceptionsSeries (ha : IsUnit a) :
    Tendsto (fun s ↦ afterExceptionsSeries a E s / normalizer s) (𝓝[>] (1 : ℝ))
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply (Paper4DirichletDensity.normalized_primeSeries_after_exceptions a ha E).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [afterExceptionsSeries_eq_sub a E (Set.mem_Ioi.mp hs)]

/-- Literal modular-congruence formulation of the corrected density. -/
theorem reduced_progression_density (r : ℕ) (hr : r.Coprime q) :
    Tendsto (fun s : ℝ ↦ (∑' n : ℕ,
      if n.Prime ∧ (n ≡ r [MOD q]) ∧ n ∉ E then (n : ℝ) ^ (-s) else 0) / normalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hu : IsUnit (r : ZMod q) :=
    ⟨ZMod.unitOfCoprime r hr, ZMod.coe_unitOfCoprime r hr⟩
  apply (normalized_afterExceptionsSeries (r : ZMod q) E hu).congr
  intro s
  congr 1
  unfold afterExceptionsSeries
  apply tsum_congr
  intro n
  by_cases hn : n ∈ E
  · simp [hn]
  · simp [hn, term, countCoeff, ZMod.natCast_eq_natCast_iff,
      div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n), ite_mul]

end
end ManuscriptAudit.Paper4PrimeDirichletExceptions

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4PrimeDirichletExceptions.afterExceptionsSeries_eq_sub,
      ``ManuscriptAudit.Paper4PrimeDirichletExceptions.normalized_afterExceptionsSeries,
      ``ManuscriptAudit.Paper4PrimeDirichletExceptions.reduced_progression_density] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
