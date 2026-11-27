import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Finset.Lattice.Fold
import PrimalitySheafVerification.ManuscriptAudit.CoulombCompactTruncationRealization

/-! Paper 10, physical p. 495, Proposition 4.15. A complete orthonormal
eigenbasis with eigenvalues bounded below would force a lower bound on
the entire symmetric operator domain. This is incompatible with the
actual compact-cut tests for the negative sign of equation (4.43). -/

namespace ManuscriptAudit.CoulombCompactEigenbasis

open CoulombCompactTruncationForm CoulombCompactTruncationRealization
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Symmetry on the full partial-operator domain and a Hilbert basis
of domain eigenvectors transfer a common eigenvalue lower bound to
the full quadratic form. -/
theorem quadratic_lower_bound_of_hilbertBasis {ι : Type*} (T : H →ₗ.[ℝ] H)
    (hSym : T.IsFormalAdjoint T) (e : HilbertBasis ι ℝ H) (lambda : ι → ℝ)
    (hDomain : ∀ i, e i ∈ T.domain)
    (hEigen : ∀ i, T ⟨e i, hDomain i⟩ = lambda i • e i)
    (c : ℝ) (hLower : ∀ i, c ≤ lambda i) (x : T.domain) :
    c * ‖(x : H)‖ ^ 2 ≤ inner ℝ (x : H) (T x) := by
  have hPt (i : ι) :
      c * (inner ℝ (x : H) (e i) * inner ℝ (e i) (x : H)) ≤
        inner ℝ (x : H) (e i) * inner ℝ (e i) (T x) := by
    have hE : inner ℝ (e i) (T x) = lambda i * inner ℝ (e i) (x : H) := by
      have hs : inner ℝ (e i) (T x) =
          inner ℝ (T ⟨e i, hDomain i⟩) (x : H) := (hSym ⟨e i, hDomain i⟩ x).symm
      rw [hs, hEigen i, real_inner_smul_left]
    have hc : inner ℝ (x : H) (e i) = inner ℝ (e i) (x : H) := real_inner_comm _ _
    rw [hc, hE]
    calc
      _ = c * (inner ℝ (e i) (x : H)) ^ 2 := by ring
      _ ≤ lambda i * (inner ℝ (e i) (x : H)) ^ 2 :=
        mul_le_mul_of_nonneg_right (hLower i) (sq_nonneg _)
      _ = _ := by ring
  have hLo := (e.hasSum_inner_mul_inner (x : H) (x : H)).mul_left c
  have hHi := e.hasSum_inner_mul_inner (x : H) (T x)
  have h := hasSum_le hPt hLo hHi
  simpa only [real_inner_self_eq_norm_sq] using h

/-- Any Hilbert basis of eigenvectors of a symmetric realization of
the compact-cut negative form has eigenvalues unbounded below. -/
theorem truncated_eigenvalues_unbounded_below {ι : Type*}
    (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (hSym : T.IsFormalAdjoint T)
    (e : HilbertBasis ι ℝ H) (lambda : ι → ℝ)
    (hDomain : ∀ i, e i ∈ T.domain)
    (hEigen : ∀ i, T ⟨e i, hDomain i⟩ = lambda i • e i)
    (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnTruncation D Y r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r) :
    ¬ BddBelow (Set.range lambda) := by
  rintro ⟨c, hc⟩
  have hLower : ∀ i, c ≤ lambda i := fun i => hc ⟨i, rfl⟩
  exact truncated_realization_has_no_lower_bound D Y hY V hV hB T test hMass hForm
    ⟨c, quadratic_lower_bound_of_hilbertBasis T hSym e lambda hDomain hEigen c hLower⟩

/-- The advertised nondecreasing ordering of a complete eigenbasis
cannot occur for the negative-form realization on this compact cut. -/
theorem truncated_eigenbasis_not_nondecreasing (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (hSym : T.IsFormalAdjoint T)
    (e : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hDomain : ∀ i, e i ∈ T.domain)
    (hEigen : ∀ i, T ⟨e i, hDomain i⟩ = lambda i • e i)
    (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnTruncation D Y r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r) :
    ¬ Monotone lambda := by
  intro hMono
  apply truncated_eigenvalues_unbounded_below D Y hY V hV hB T hSym e lambda hDomain hEigen
    test hMass hForm
  refine ⟨lambda 0, ?_⟩
  rintro a ⟨n, rfl⟩
  exact hMono (Nat.zero_le n)

private theorem bddBelow_range_of_tendsto_atTop (lambda : ℕ → ℝ)
    (h : Filter.Tendsto lambda Filter.atTop Filter.atTop) : BddBelow (Set.range lambda) := by
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp h) 0
  have hNonempty : (Finset.range (N + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let c := min ((Finset.range (N + 1)).inf' hNonempty lambda) 0
  refine ⟨c, ?_⟩
  rintro a ⟨n, rfl⟩
  by_cases hn : n ≤ N
  · have hMem : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
    exact (min_le_left _ _).trans (Finset.inf'_le lambda hMem)
  · exact (min_le_right _ _).trans (hN n (lt_of_not_ge hn).le)

/-- The eigenvalues of a complete eigenbasis cannot tend to plus
infinity under any enumeration by the natural numbers. -/
theorem truncated_eigenbasis_not_tendsto_atTop (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (hSym : T.IsFormalAdjoint T)
    (e : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hDomain : ∀ i, e i ∈ T.domain)
    (hEigen : ∀ i, T ⟨e i, hDomain i⟩ = lambda i • e i)
    (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnTruncation D Y r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r) :
    ¬ Filter.Tendsto lambda Filter.atTop Filter.atTop := by
  intro h
  exact truncated_eigenvalues_unbounded_below D Y hY V hV hB T hSym e lambda hDomain hEigen
    test hMass hForm (bddBelow_range_of_tendsto_atTop lambda h)

end
end ManuscriptAudit.CoulombCompactEigenbasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombCompactEigenbasis.quadratic_lower_bound_of_hilbertBasis,
      ``ManuscriptAudit.CoulombCompactEigenbasis.truncated_eigenvalues_unbounded_below,
      ``ManuscriptAudit.CoulombCompactEigenbasis.truncated_eigenbasis_not_nondecreasing,
      ``ManuscriptAudit.CoulombCompactEigenbasis.truncated_eigenbasis_not_tendsto_atTop] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
