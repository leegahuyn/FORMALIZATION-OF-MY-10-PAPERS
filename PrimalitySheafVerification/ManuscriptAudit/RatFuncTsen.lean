import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Fintype.EquivFin
import PrimalitySheafVerification.ManuscriptAudit.HomogeneousPolynomialSubstitution
import PrimalitySheafVerification.ManuscriptAudit.PolynomialCommonZero
import PrimalitySheafVerification.ManuscriptAudit.RatFuncHomogeneousDenominator

/-!
# The homogeneous equation form of Tsen's theorem for K(t)

Evaluate a homogeneous form at univariate polynomials with free
coefficients. Comparing coefficients gives fewer polynomial equations
than unknowns. The Nullstellensatz dimension bound produces a nonzero
coefficient vector, and clearing denominators then handles K(t).
-/

namespace ManuscriptAudit.RatFuncTsen

open MvPolynomial
open scoped BigOperators

private theorem eval_origin_of_homogeneous {K ι : Type*} [CommRing K]
    {P : MvPolynomial ι K} {d : ℕ} (hP : P.IsHomogeneous d) (hd : 0 < d) :
    eval (0 : ι → K) P = 0 := by
  classical
  rw [← eval₂_id, eval₂_eq]
  apply Finset.sum_eq_zero
  intro m hm
  have hn : m.support.Nonempty := by
    by_contra he
    have h := hP.degree_eq_sum_deg_support hm
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at h
    exact (Nat.ne_of_gt hd) h
  obtain ⟨i, hi⟩ := hn
  have hp : (0 : ι → K) i ^ m i = 0 :=
    zero_pow (Finsupp.mem_support_iff.mp hi)
  rw [Finset.prod_eq_zero hi hp, mul_zero]

private theorem eval_substitution {K ι τ : Type*} [CommRing K]
    (P : MvPolynomial ι (Polynomial K)) (g : ι → Polynomial (MvPolynomial τ K))
    (v : τ → K) :
    (P.eval₂ (Polynomial.mapRingHom MvPolynomial.C) g).map (MvPolynomial.eval v) =
      P.eval₂ (RingHom.id (Polynomial K)) (fun i => (g i).map (MvPolynomial.eval v)) := by
  let e := Polynomial.mapRingHom (MvPolynomial.eval v)
  let c := Polynomial.mapRingHom (MvPolynomial.C : K →+* MvPolynomial τ K)
  have hComp : e.comp c = RingHom.id (Polynomial K) := by
    apply RingHom.ext
    intro p
    apply Polynomial.ext
    intro i
    change ((p.map MvPolynomial.C).map (MvPolynomial.eval v)).coeff i = p.coeff i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, MvPolynomial.eval_C]
  have h := MvPolynomial.hom_eval₂ P c e g
  rw [hComp] at h
  exact h

private noncomputable def genericPolynomial {K : Type*} [CommRing K] {n N : ℕ}
    (e : Fin n × Fin (N + 1) ≃ Fin (n * (N + 1))) (i : Fin n) :
    Polynomial (MvPolynomial (Fin (n * (N + 1))) K) :=
  ∑ j : Fin (N + 1), Polynomial.monomial j.val (X (e (i, j)))

private theorem genericPolynomial_coeff {K : Type*} [CommRing K] {n N : ℕ}
    (e : Fin n × Fin (N + 1) ≃ Fin (n * (N + 1))) (i : Fin n) (j : Fin (N + 1)) :
    (genericPolynomial (K := K) e i).coeff j.val = X (e (i, j)) := by
  let c : Polynomial (MvPolynomial (Fin (n * (N + 1))) K) →+
      MvPolynomial (Fin (n * (N + 1))) K :=
    { toFun := fun p => p.coeff j.val
      map_zero' := Polynomial.coeff_zero _
      map_add' := fun p q => Polynomial.coeff_add p q _ }
  change c (∑ b : Fin (N + 1), Polynomial.monomial b.val (X (e (i, b)))) = _
  rw [map_sum]
  simp only [show ∀ p, c p = p.coeff j.val from fun _ => rfl, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact if_neg (fun h => hb (Fin.ext h))
  · simp

/-- The nonzero solution can already be chosen over the polynomial ring
when the form has polynomial coefficients. -/
theorem exists_polynomial_zero {K : Type*} [Field K] [IsAlgClosed K] {n d : ℕ}
    (P : MvPolynomial (Fin n) (Polynomial K)) (hP : P.IsHomogeneous d)
    (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → Polynomial K, x ≠ 0 ∧ aeval x P = 0 := by
  classical
  let L := P.support.sup (fun m => (P.coeff m).natDegree)
  let N := L + 1
  let A := Fin (n * (N + 1))
  let e : Fin n × Fin (N + 1) ≃ A := Fintype.equivFinOfCardEq (by
    simp [Fintype.card_prod])
  let g := genericPolynomial (K := K) e
  let Φ : Polynomial (MvPolynomial A K) :=
    P.eval₂ (Polynomial.mapRingHom MvPolynomial.C) g
  have hL (m) (hm : m ∈ P.support) : (P.coeff m).natDegree ≤ L :=
    Finset.le_sup (f := fun m => (P.coeff m).natDegree) hm
  have hg (i : Fin n) : (g i).natDegree ≤ N := by
    change (∑ j : Fin (N + 1), Polynomial.monomial j.val (X (e (i, j)))).natDegree ≤ N
    apply HomogeneousPolynomialSubstitution.natDegree_sum_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ j.isLt)
  have hΦ : Φ.natDegree ≤ L + d * N :=
    HomogeneousPolynomialSubstitution.natDegree_eval₂_le P hP hL MvPolynomial.C g hg
  have hcount : L + d * N + 1 < n * (N + 1) := by
    have h : L + d * N + 1 < (d + 1) * (N + 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      have hN : L < N := Nat.lt_succ_self L
      omega
    exact h.trans_le (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hn))
  have hGZero (i : Fin n) : (g i).map (MvPolynomial.eval (0 : A → K)) = 0 := by
    change (∑ j : Fin (N + 1), Polynomial.monomial j.val (X (e (i, j)))).map _ = 0
    rw [Polynomial.map_sum]
    simp [Polynomial.map_monomial]
  have hΦZero : Φ.map (MvPolynomial.eval (0 : A → K)) = 0 := by
    have h := eval_substitution P g (0 : A → K)
    have harg : (fun i => (g i).map (MvPolynomial.eval (0 : A → K))) = 0 :=
      funext hGZero
    rw [harg, eval₂_id] at h
    exact h.trans (eval_origin_of_homogeneous hP hd)
  let f : Fin (L + d * N + 1) → MvPolynomial A K := fun j => Φ.coeff j.val
  have hfZero (j) : aeval (0 : A → K) (f j) = 0 := by
    change MvPolynomial.eval (0 : A → K) (Φ.coeff j.val) = 0
    rw [← Polynomial.coeff_map, hΦZero, Polynomial.coeff_zero]
  obtain ⟨v, hv, hf⟩ := PolynomialCommonZero.exists_nonzero_common_zero K hcount f hfZero
  let y := fun i => (g i).map (MvPolynomial.eval v)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hv
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have h : (y i).coeff j.val = v (e (i, j)) := by
      change ((g i).map (MvPolynomial.eval v)).coeff j.val = _
      rw [Polynomial.coeff_map, genericPolynomial_coeff, MvPolynomial.eval_X]
    rw [hy, Pi.zero_apply, Polynomial.coeff_zero] at h
    exact h.symm
  · have hMap : Φ.map (MvPolynomial.eval v) = 0 := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      by_cases hk : k < L + d * N + 1
      · exact hf ⟨k, hk⟩
      · have hd' : Φ.natDegree < k := hΦ.trans_lt (by omega)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd', map_zero]
    exact (eval_substitution P g v).symm.trans hMap

/-- Tsen's degree bound over the rational function field of an algebraically
closed field. -/
theorem exists_ratFunc_zero {K : Type*} [Field K] [IsAlgClosed K] {n d : ℕ}
    (P : MvPolynomial (Fin n) (RatFunc K)) (hP : P.IsHomogeneous d)
    (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → RatFunc K, x ≠ 0 ∧ aeval x P = 0 := by
  obtain ⟨q, hq, Q, hQ, h⟩ := RatFuncHomogeneousDenominator.clearDenominator K P hP
  obtain ⟨x, hx, hxQ⟩ := exists_polynomial_zero Q hQ hd hn
  exact RatFuncHomogeneousDenominator.evaluateCleared K hq h hx hxQ

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.exists_polynomial_zero,
      ``ManuscriptAudit.RatFuncTsen.exists_ratFunc_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
