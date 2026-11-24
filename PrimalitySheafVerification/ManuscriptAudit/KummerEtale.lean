import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! Adjoining a root of a unit gives a finite faithfully flat algebra for positive
degree. The derivative criterion yields étaleness when the degree is invertible.
These are algebraic prerequisites for the Kummer cover. -/

namespace ManuscriptAudit.KummerEtale

open Polynomial

noncomputable section

variable {A : Type*} [CommRing A]

def kummerPolynomial (d : ℕ) (a : A) : Polynomial A :=
  X ^ d - C a

theorem kummer_monic {d : ℕ} (hd : 0 < d) (a : A) :
    (kummerPolynomial d a).Monic :=
  Polynomial.monic_X_pow_sub_C a (Nat.ne_of_gt hd)

theorem kummer_root_pow (d : ℕ) (a : A) :
    AdjoinRoot.root (kummerPolynomial d a) ^ d =
      algebraMap A (AdjoinRoot (kummerPolynomial d a)) a := by
  have h : Polynomial.aeval (AdjoinRoot.root (kummerPolynomial d a))
      (kummerPolynomial d a) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  exact sub_eq_zero.mp (by
    simpa only [kummerPolynomial, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] using h)

theorem kummer_root_isUnit {d : ℕ} (hd : 0 < d) {a : A} (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root (kummerPolynomial d a)) := by
  have hpow : IsUnit (AdjoinRoot.root (kummerPolynomial d a) ^ d) := by
    rw [kummer_root_pow]
    exact ha.map (algebraMap A _)
  exact isUnit_of_dvd_unit (dvd_pow_self _ (Nat.ne_of_gt hd)) hpow

theorem kummer_derivative_value (d : ℕ) (a : A) :
    AdjoinRoot.mk (kummerPolynomial d a) (kummerPolynomial d a).derivative =
      algebraMap A (AdjoinRoot (kummerPolynomial d a)) (d : A) *
        AdjoinRoot.root (kummerPolynomial d a) ^ (d - 1) := by
  rw [← AdjoinRoot.aeval_eq]
  simp only [kummerPolynomial, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]

theorem adjoinRoot_etale_of_derivative_unit {f : Polynomial A} (hf : f.Monic)
    (hu : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale A (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (g := f) (↑(u⁻¹) : AdjoinRoot f)
  have hm : AdjoinRoot.mk f (f.derivative * q - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← hu, hq, Units.mul_inv, sub_self]
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_zero.mp hm
  have hcond : ∃ p₁ p₂ : Polynomial A, ∃ n : ℕ,
      f.derivative * p₁ + f * p₂ = (1 : Polynomial A) ^ n := by
    refine ⟨q, -r, 0, ?_⟩
    rw [pow_zero, mul_neg, ← sub_eq_add_neg, ← hr, sub_sub_cancel]
  let P : StandardEtalePair A := ⟨f, hf, 1, hcond⟩
  let S := Localization.Away (AdjoinRoot.mk P.f P.g)
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    change IsUnit (AdjoinRoot.mk f 1)
    simp
  let e₁ : P.Ring ≃ₐ[A] S := P.equivAwayAdjoinRoot
  let e₂ : S ≃ₐ[A] AdjoinRoot P.f :=
    (IsLocalization.atUnit (AdjoinRoot P.f) S _ hunit).symm.restrictScalars A
  exact Algebra.Etale.of_equiv (e₁.trans e₂)

theorem kummer_etale {d : ℕ} (hpos : 0 < d) (hd : IsUnit (d : A))
    {a : A} (ha : IsUnit a) :
    Algebra.Etale A (AdjoinRoot (kummerPolynomial d a)) := by
  refine adjoinRoot_etale_of_derivative_unit (kummer_monic hpos a) ?_
  rw [kummer_derivative_value]
  exact (hd.map (algebraMap A _)).mul ((kummer_root_isUnit hpos ha).pow _)

theorem kummer_module_finite {d : ℕ} (hpos : 0 < d) (a : A) :
    Module.Finite A (AdjoinRoot (kummerPolynomial d a)) :=
  (kummer_monic hpos a).finite_adjoinRoot

theorem kummer_faithfullyFlat {d : ℕ} (hpos : 0 < d) (a : A) :
    Module.FaithfullyFlat A (AdjoinRoot (kummerPolynomial d a)) := by
  letI : Module.Free A (AdjoinRoot (kummerPolynomial d a)) :=
    (kummer_monic hpos a).free_adjoinRoot
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI : Subsingleton A := hA
    refine ⟨inferInstance, ?_⟩
    intro m hm
    have ht : m = ⊤ := (Ideal.eq_top_iff_one m).mpr (by
      rw [Subsingleton.elim (1 : A) 0]
      exact m.zero_mem)
    exact (hm.ne_top ht).elim
  · letI : Nontrivial A := hA
    have hn : 0 < (kummerPolynomial d a).natDegree := by
      simpa only [kummerPolynomial, Polynomial.natDegree_X_pow_sub_C] using hpos
    haveI : Nonempty (Fin (kummerPolynomial d a).natDegree) := ⟨⟨0, hn⟩⟩
    exact Module.FaithfullyFlat.of_linearEquiv A
      (Fin (kummerPolynomial d a).natDegree →₀ A)
      (AdjoinRoot.powerBasisAux' (kummer_monic hpos a)).repr

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``kummer_monic, ``kummer_root_pow, ``kummer_root_isUnit,
      ``kummer_derivative_value, ``adjoinRoot_etale_of_derivative_unit, ``kummer_etale,
      ``kummer_module_finite, ``kummer_faithfullyFlat] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.KummerEtale
