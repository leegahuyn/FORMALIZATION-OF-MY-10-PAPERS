import Mathlib.Algebra.MvPolynomial.Division
import PrimalitySheafVerification.Spt5

/-!
# The first cotangent homology of a singular nodal curve

Paper 2, pp. 27–28 and 42, asserts that vanishing of the first cotangent
homology implies smoothness for a curve fiber. The affine node provides a
counterexample. The calculation uses the conormal complex for the principal
relation and Mathlib's presentation-independent first cotangent homology.
-/

namespace ManuscriptAudit.NodalCotangent

open Algebra MvPolynomial
open scoped nonZeroDivisors

noncomputable section

variable (k : Type*) [Field k]

private abbrev R := MvPolynomial (Fin 2) k
private abbrev relation : R k := X 0 * X 1
private abbrev I : Ideal (R k) := Ideal.span {relation k}

/-- The affine node cut out by the product of the two coordinates. -/
abbrev NodeRing := R k ⧸ I k

private abbrev nodeVar (i : Fin 2) : NodeRing k := Ideal.Quotient.mk (I k) (X i)

private def G : Algebra.Generators k (NodeRing k) (Fin 2) :=
  Algebra.Generators.naive

private theorem Gker : (G k).toExtension.ker = I k :=
  Algebra.Generators.ker_naive _ _

private def relInKer : (G k).toExtension.ker := by
  refine ⟨relation k, ?_⟩
  rw [Gker]
  exact Ideal.mem_span_singleton_self _

private def gen : (G k).toExtension.Cotangent :=
  Extension.Cotangent.mk (relInKer k)

private theorem relationRegular : relation k ∈ ((G k).toExtension.Ring)⁰ := by
  change relation k ∈ (R k)⁰
  exact mem_nonZeroDivisors_of_ne_zero
    (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))

private def conormal : NodeRing k ≃ₗ[NodeRing k] (G k).toExtension.Cotangent :=
  Spt5.extCotangentEquiv (G k).toExtension (relation k) (relationRegular k) (Gker k)

private theorem conormal_one : conormal k 1 = gen k :=
  Spt5.extCotangentEquiv_one (G k).toExtension (relation k) (relationRegular k) (Gker k)

private theorem conormal_apply (s : NodeRing k) : conormal k s = s • gen k := by
  rw [← conormal_one k, ← map_smul, smul_eq_mul, mul_one]

private theorem repr_derivative (i : Fin 2) :
    (G k).cotangentSpaceBasis.repr ((G k).toExtension.cotangentComplex (gen k)) i =
      aeval (G k).val (pderiv i (relation k)) :=
  Spt5.cotangentComplex_repr (G k) (relInKer k) i

private theorem derivative_zero :
    (G k).cotangentSpaceBasis.repr ((G k).toExtension.cotangentComplex (gen k)) 0 =
      nodeVar k 1 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [repr_derivative, relation, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (R := k) _ _ h, G]

private theorem derivative_one :
    (G k).cotangentSpaceBasis.repr ((G k).toExtension.cotangentComplex (gen k)) 1 =
      nodeVar k 0 := by
  have h : (0 : Fin 2) ≠ 1 := by decide
  simp [repr_derivative, relation, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (R := k) _ _ h, G]

private theorem common_annihilator (s : NodeRing k)
    (hx : s * nodeVar k 0 = 0) (hy : s * nodeVar k 1 = 0) : s = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := I k) s
  change Ideal.Quotient.mk (I k) g * Ideal.Quotient.mk (I k) (X 0) = 0 at hx
  change Ideal.Quotient.mk (I k) g * Ideal.Quotient.mk (I k) (X 1) = 0 at hy
  rw [← map_mul] at hx hy
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hy)
  have hY : (X (1 : Fin 2) : R k) ∣ g := by
    refine ⟨u, (MvPolynomial.X_mul_cancel_left_iff (i := (0 : Fin 2))).mp ?_⟩
    calc
      X 0 * g = g * X 0 := mul_comm _ _
      _ = relation k * u := hu
      _ = X 0 * (X 1 * u) := mul_assoc _ _ _
  have hX : (X (0 : Fin 2) : R k) ∣ g := by
    refine ⟨v, (MvPolynomial.X_mul_cancel_left_iff (i := (1 : Fin 2))).mp ?_⟩
    calc
      X 1 * g = g * X 1 := mul_comm _ _
      _ = relation k * v := hv
      _ = X 1 * (X 0 * v) := by
        change (X 0 * X 1 : R k) * v = _
        ac_rfl
  obtain ⟨t, ht⟩ := hY
  have hprime : Prime (X (0 : Fin 2) : R k) := by
    first | exact MvPolynomial.prime_X | exact MvPolynomial.X_prime
  have hXt : (X (0 : Fin 2) : R k) ∣ t := by
    have hprod : (X (0 : Fin 2) : R k) ∣ X 1 * t := by rwa [← ht]
    exact (hprime.dvd_mul.mp hprod).resolve_left (by rw [MvPolynomial.X_dvd_X]; decide)
  obtain ⟨w, hw⟩ := hXt
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨w, ?_⟩
  rw [ht, hw]
  change (X 1 : R k) * (X 0 * w) = (X 0 * X 1) * w
  ac_rfl

/-- The two coordinate classes have zero common annihilator, so the actual
first cotangent homology of the node vanishes. -/
theorem node_h1Cotangent_subsingleton :
    Subsingleton (Algebra.H1Cotangent k (NodeRing k)) := by
  letI : Algebra.FormallySmooth k (G k).toExtension.Ring := by
    change Algebra.FormallySmooth k (R k)
    infer_instance
  apply ((G k).toExtension.cotangentComplex_injective_iff).mp
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, rfl⟩ := (conormal k).surjective z
  have hy := congrArg (fun q => (G k).cotangentSpaceBasis.repr q 0) hz
  have hx := congrArg (fun q => (G k).cotangentSpaceBasis.repr q 1) hz
  simp only [conormal_apply, map_smul, Finsupp.smul_apply, derivative_zero,
    derivative_one, smul_eq_mul, map_zero, Finsupp.zero_apply] at hx hy
  rw [common_annihilator k s hx hy, map_zero]

private def origin : NodeRing k →+* k :=
  Ideal.Quotient.lift (I k) (aeval (fun _ : Fin 2 => (0 : k))).toRingHom (by
    intro f hf
    have hf' : relation k ∣ f := Ideal.mem_span_singleton.mp hf
    obtain ⟨g, rfl⟩ := hf'
    simp [relation])

private theorem origin_nodeVar (i : Fin 2) : origin k (nodeVar k i) = 0 := by
  simp [origin, nodeVar]

/-- A splitting of the conormal differential would give a linear combination
of the two coordinates equal to 1, contrary to evaluation at the origin. -/
theorem node_not_smooth : ¬ Algebra.Smooth k (NodeRing k) := by
  intro h
  letI : Algebra.FormallySmooth k (G k).toExtension.Ring := by
    change Algebra.FormallySmooth k (R k)
    infer_instance
  obtain ⟨ret, hret⟩ := ((G k).toExtension.formallySmooth_iff_split_injection).mp h.formallySmooth
  let b := (G k).cotangentSpaceBasis
  have hd : (G k).toExtension.cotangentComplex (gen k) =
      nodeVar k 1 • b 0 + nodeVar k 0 • b 1 := by
    apply b.repr.injective
    ext i
    fin_cases i
    · simpa [b, derivative_zero]
    · simpa [b, derivative_one]
  have he : ret ((G k).toExtension.cotangentComplex (gen k)) = gen k :=
    LinearMap.congr_fun hret (gen k)
  rw [hd, map_add, map_smul, map_smul] at he
  have hw := congrArg (fun z => (conormal k).symm z) he
  have hg : (conormal k).symm (gen k) = 1 := by
    rw [← conormal_one k, LinearEquiv.symm_apply_apply]
  simp only [map_add, map_smul, smul_eq_mul, hg] at hw
  have ht := congrArg (origin k) hw
  exact zero_ne_one (show (0 : k) = 1 by
    simpa only [map_add, map_mul, origin_nodeVar, zero_mul, add_zero, map_one] using ht)

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Paper 2, pp. 27–28 and 42. The affine node over the residue field F₅
has vanishing first cotangent homology and is singular. -/
theorem paper2_node_F5_cotangent_vanishing_and_singular :
    Subsingleton (Algebra.H1Cotangent (ZMod 5) (NodeRing (ZMod 5))) ∧
      ¬ Algebra.Smooth (ZMod 5) (NodeRing (ZMod 5)) :=
  ⟨node_h1Cotangent_subsingleton _, node_not_smooth _⟩

end

end ManuscriptAudit.NodalCotangent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.NodalCotangent.node_h1Cotangent_subsingleton,
    ``ManuscriptAudit.NodalCotangent.node_not_smooth,
    ``ManuscriptAudit.NodalCotangent.paper2_node_F5_cotangent_vanishing_and_singular] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
