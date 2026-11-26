import Lean.Util.CollectAxioms
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A primitive monomial relation in the two-dimensional torus gives a Laurent line. -/

namespace ManuscriptAudit.CoprimeTorusAlgebra

noncomputable section

variable (R : Type*) [CommRing R]

private abbrev Lattice := ℤ × ℤ
abbrev TwoTorus := AddMonoidAlgebra R Lattice

private def monomial (v : Lattice) : TwoTorus R := AddMonoidAlgebra.single v 1

def relationIdeal (m n : ℕ) : Ideal (TwoTorus R) :=
  Ideal.span {monomial R (m, 0) - monomial R (0, n)}

abbrev Curve (m n : ℕ) := TwoTorus R ⧸ relationIdeal R m n

private def weight (m n : ℕ) : Lattice →+ ℤ where
  toFun v := (n : ℤ) * v.1 + (m : ℤ) * v.2
  map_zero' := by simp
  map_add' v w := by
    change (n : ℤ) * (v.1 + w.1) + (m : ℤ) * (v.2 + w.2) =
      (n : ℤ) * v.1 + (m : ℤ) * v.2 + ((n : ℤ) * w.1 + (m : ℤ) * w.2)
    ring

private def liftWeight (m n : ℕ) : ℤ →+ Lattice where
  toFun j := (Nat.gcdA n m * j, Nat.gcdB n m * j)
  map_zero' := by simp
  map_add' i j := by
    apply Prod.ext <;> simp [mul_add]

private theorem bezout {m n : ℕ} (h : m.Coprime n) :
    (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m = 1 := by
  have hg : Nat.gcd n m = 1 := h.symm
  simpa only [hg, Nat.cast_one] using (Nat.gcd_eq_gcd_ab n m).symm

private theorem weight_liftWeight {m n : ℕ} (h : m.Coprime n) (z : ℤ) :
    weight m n (liftWeight m n z) = z := by
  change (n : ℤ) * (Nat.gcdA n m * z) + (m : ℤ) * (Nat.gcdB n m * z) = z
  calc
    _ = ((n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m) * z := by ring
    _ = z := by rw [bezout h, one_mul]

private theorem lattice_expansion {m n : ℕ} (h : m.Coprime n) (v : Lattice) :
    v = liftWeight m n (weight m n v) +
      (Nat.gcdB n m * v.1 - Nat.gcdA n m * v.2) • ((m : ℤ), -(n : ℤ)) := by
  rcases v with ⟨i, j⟩
  apply Prod.ext
  · change i = Nat.gcdA n m * ((n : ℤ) * i + (m : ℤ) * j) +
      (Nat.gcdB n m * i - Nat.gcdA n m * j) • (m : ℤ)
    simp only [zsmul_eq_mul, Int.cast_id]
    linear_combination -i * (bezout h)
  · change j = Nat.gcdB n m * ((n : ℤ) * i + (m : ℤ) * j) +
      (Nat.gcdB n m * i - Nat.gcdA n m * j) • (-(n : ℤ))
    simp only [zsmul_eq_mul, Int.cast_id]
    linear_combination -j * (bezout h)

private def project (m n : ℕ) : TwoTorus R →ₐ[R] LaurentPolynomial R :=
  AddMonoidAlgebra.mapDomainAlgHom R R (weight m n)

private def quotientMap (m n : ℕ) : TwoTorus R →ₐ[R] Curve R m n :=
  Ideal.Quotient.mkₐ R (relationIdeal R m n)

private def quotientMonomial (m n : ℕ) (v : Lattice) : Curve R m n :=
  quotientMap R m n (monomial R v)

private theorem mapDomain_monomial {A B : Type*} [AddMonoid A] [AddMonoid B]
    (f : A →+ B) (a : A) :
    AddMonoidAlgebra.mapDomainAlgHom R R f (AddMonoidAlgebra.single a 1) =
      AddMonoidAlgebra.single (f a) 1 := by
  change AddMonoidAlgebra.mapDomain f (AddMonoidAlgebra.single a 1) = _
  simp

private theorem project_monomial (m n : ℕ) (v : Lattice) :
    project R m n (monomial R v) = AddMonoidAlgebra.single (weight m n v) 1 :=
  mapDomain_monomial R (weight m n) v

private theorem relation_in_kernel (m n : ℕ) :
    relationIdeal R m n ≤ RingHom.ker (project R m n).toRingHom := by
  apply Ideal.span_le.mpr
  intro v hv
  rcases Set.mem_singleton_iff.mp hv with rfl
  change project R m n (monomial R (m, 0) - monomial R (0, n)) = 0
  rw [map_sub, project_monomial, project_monomial]
  have he : weight m n ((m : ℤ), 0) = weight m n (0, (n : ℤ)) := by
    change (n : ℤ) * m + (m : ℤ) * 0 = (n : ℤ) * 0 + (m : ℤ) * n
    ring
  rw [he, sub_self]

private def forward (m n : ℕ) : Curve R m n →ₐ[R] LaurentPolynomial R where
  toRingHom := Ideal.Quotient.lift (relationIdeal R m n) (project R m n).toRingHom
    (fun _ hr => relation_in_kernel R m n hr)
  commutes' r := (project R m n).commutes r

private def backward (m n : ℕ) : LaurentPolynomial R →ₐ[R] Curve R m n :=
  (quotientMap R m n).comp (AddMonoidAlgebra.mapDomainAlgHom R R (liftWeight m n))

private theorem quotientMonomial_add (m n : ℕ) (v w : Lattice) :
    quotientMonomial R m n (v + w) =
      quotientMonomial R m n v * quotientMonomial R m n w := by
  unfold quotientMonomial
  rw [← map_mul]
  simp [monomial]

private theorem quotientMonomial_zero (m n : ℕ) : quotientMonomial R m n 0 = 1 := by
  change quotientMap R m n (1 : TwoTorus R) = 1
  exact map_one _

private theorem quotientMonomial_relation (m n : ℕ) :
    quotientMonomial R m n ((m : ℤ), -(n : ℤ)) = 1 := by
  have hf : quotientMonomial R m n ((m : ℤ), 0) =
      quotientMonomial R m n (0, (n : ℤ)) := by
    apply sub_eq_zero.mp
    rw [quotientMonomial, quotientMonomial, ← map_sub]
    exact Ideal.Quotient.mk_singleton_self _
  calc
    _ = quotientMonomial R m n ((m : ℤ), 0) *
        quotientMonomial R m n (0, -(n : ℤ)) := by
          rw [← quotientMonomial_add]
          congr 1
          ext <;> simp
    _ = 1 := by
      have hv : ((0, (n : ℤ)) : Lattice) + (0, -(n : ℤ)) = 0 := by
        apply Prod.ext <;> simp
      rw [hf, ← quotientMonomial_add, hv, quotientMonomial_zero]

private def trivialExponents (m n : ℕ) : AddSubgroup Lattice where
  carrier := {v | quotientMonomial R m n v = 1}
  zero_mem' := quotientMonomial_zero R m n
  add_mem' {v w} hv hw := by
    change quotientMonomial R m n v = 1 at hv
    change quotientMonomial R m n w = 1 at hw
    change quotientMonomial R m n (v + w) = 1
    rw [quotientMonomial_add, hv, hw, one_mul]
  neg_mem' {v} hv := by
    change quotientMonomial R m n v = 1 at hv
    change quotientMonomial R m n (-v) = 1
    have he := quotientMonomial_add R m n v (-v)
    rw [add_neg_cancel, quotientMonomial_zero, hv, one_mul] at he
    exact he.symm

private theorem quotientMonomial_liftWeight {m n : ℕ} (h : m.Coprime n) (v : Lattice) :
    quotientMonomial R m n (liftWeight m n (weight m n v)) =
      quotientMonomial R m n v := by
  have hi : ((m : ℤ), -(n : ℤ)) ∈ trivialExponents R m n :=
    quotientMonomial_relation R m n
  have hj := (trivialExponents R m n).zsmul_mem hi
    (Nat.gcdB n m * v.1 - Nat.gcdA n m * v.2)
  change quotientMonomial R m n
    ((Nat.gcdB n m * v.1 - Nat.gcdA n m * v.2) • ((m : ℤ), -(n : ℤ))) = 1 at hj
  conv_rhs => rw [lattice_expansion h v, quotientMonomial_add, hj, mul_one]

private theorem hom_ext_monomials {A B : Type*} [AddMonoid A] [CommRing B] [Algebra R B]
    {f g : AddMonoidAlgebra R A →ₐ[R] B}
    (h : ∀ v : A, f (AddMonoidAlgebra.single v 1) = g (AddMonoidAlgebra.single v 1)) : f = g := by
  apply AlgHom.ext
  intro x
  refine AddMonoidAlgebra.induction_on x ?_ ?_ ?_
  · exact h
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes, hx]

private theorem backward_monomial (m n : ℕ) (j : ℤ) :
    backward R m n (AddMonoidAlgebra.single j 1) = quotientMonomial R m n (liftWeight m n j) := by
  change quotientMap R m n (AddMonoidAlgebra.mapDomainAlgHom R R (liftWeight m n)
    (AddMonoidAlgebra.single j 1)) = _
  rw [mapDomain_monomial]
  rfl

/-- The actual quotient of the Laurent torus algebra by U^m = V^n is a Laurent line. -/
def coordinateEquiv {m n : ℕ} (h : m.Coprime n) : Curve R m n ≃ₐ[R] LaurentPolynomial R := by
  refine AlgEquiv.ofAlgHom (forward R m n) (backward R m n) ?_ ?_
  · apply hom_ext_monomials R
    intro j
    change forward R m n (backward R m n (AddMonoidAlgebra.single j 1)) =
      AddMonoidAlgebra.single j 1
    rw [backward_monomial]
    change project R m n (monomial R (liftWeight m n j)) = _
    rw [project_monomial, weight_liftWeight h]
  · have eq :
        ((backward R m n).comp (forward R m n)).comp (quotientMap R m n) =
          quotientMap R m n := by
      apply hom_ext_monomials R
      intro v
      change backward R m n (project R m n (monomial R v)) = quotientMonomial R m n v
      rw [project_monomial, backward_monomial, quotientMonomial_liftWeight R h]
    apply AlgHom.ext
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact DFunLike.congr_fun eq z

end
end ManuscriptAudit.CoprimeTorusAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CoprimeTorusAlgebra.coordinateEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
