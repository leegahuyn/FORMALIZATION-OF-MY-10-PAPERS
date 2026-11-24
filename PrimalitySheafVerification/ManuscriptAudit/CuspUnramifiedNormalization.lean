import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Unramified.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured

/-!
# Sections of unramified affine schemes over the cusp normalization

An algebra map from a formally unramified cusp algebra to the polynomial
normalization factors uniquely through the cusp coordinate ring. The proof
compares the two reductions to the square-zero neighborhood of the origin.
-/

namespace ManuscriptAudit.CuspUnramifiedNormalization

open Polynomial CuspDelta CuspPunctured

noncomputable section

variable (K : Type*) [Field K]

private abbrev originIdeal : Ideal (cuspSquareQuotient K) :=
  Ideal.span {(cuspSquareReduction K) (X : Polynomial K)}

private theorem originIdeal_square : (originIdeal K) ^ 2 = ⊥ := by
  change (Ideal.span {(cuspSquareReduction K) (X : Polynomial K)}) ^ 2 = ⊥
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, ← map_pow]
  change Ideal.Quotient.mk (Ideal.span {((X : Polynomial K) ^ 2)}) (X ^ 2) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

variable {P : Type*} [CommRing P] [Algebra (CuspSubalgebra K) P]
variable [Algebra.FormallyUnramified (CuspSubalgebra K) P]

/-- Every image in the normalization of a formally unramified cusp
algebra already lies in the cusp coordinate subalgebra. -/
theorem image_mem_cusp (f : P →ₐ[CuspSubalgebra K] Polynomial K) (p : P) :
    f p ∈ CuspSubalgebra K := by
  let q := cuspSquareReduction K
  let c : Polynomial K →+* cuspSquareQuotient K := q.comp (C.comp Polynomial.constantCoeff)
  letI : Algebra (CuspSubalgebra K) (cuspSquareQuotient K) :=
    (q.comp (algebraMap (CuspSubalgebra K) (Polynomial K))).toAlgebra
  let qA : Polynomial K →ₐ[CuspSubalgebra K] cuspSquareQuotient K :=
    { q with commutes' := fun _ => rfl }
  let cA : Polynomial K →ₐ[CuspSubalgebra K] cuspSquareQuotient K :=
    { c with
      commutes' := fun a => by
        change q (C ((a : Polynomial K).coeff 0)) = q (a : Polynomial K)
        exact ((cusp_square_reduction_eq_constant_iff K _ _).2
          ⟨rfl, (cusp_mem_iff_coeff_one_zero K _).1 a.property⟩).symm }
  have h :
      (Ideal.Quotient.mkₐ (CuspSubalgebra K) (originIdeal K)).comp qA =
        (Ideal.Quotient.mkₐ (CuspSubalgebra K) (originIdeal K)).comp cA := by
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk (originIdeal K) (q x) =
      Ideal.Quotient.mk (originIdeal K) (q (C (x.coeff 0)))
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    apply Ideal.mem_span_singleton.mpr
    apply map_dvd q
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero, sub_self]
  let t := (UnramifiedEqualizerSections.sectionsEquiv (P := P)
    (originIdeal K) (originIdeal_square K) qA cA h).symm f
  have hp : q (f p) = q (C ((f p).coeff 0)) :=
    (AlgHom.mem_equalizer qA cA _).mp (show f p ∈ AlgHom.equalizer qA cA from (t p).property)
  exact (cusp_mem_iff_coeff_one_zero K _).2
    ((cusp_square_reduction_eq_constant_iff K _ _).1 hp).2

/-- The unique factor of a normalization-valued section through the cusp. -/
def factorThroughCusp (f : P →ₐ[CuspSubalgebra K] Polynomial K) :
    P →ₐ[CuspSubalgebra K] CuspSubalgebra K where
  toFun p := ⟨f p, image_mem_cusp K f p⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x y)
  commutes' a := Subtype.ext (f.commutes a)

/-- The normalization introduces no additional sections of an affine
formally unramified morphism over the cusp. -/
def cuspSectionsEquiv :
    (P →ₐ[CuspSubalgebra K] CuspSubalgebra K) ≃
      (P →ₐ[CuspSubalgebra K] Polynomial K) where
  toFun f := (Algebra.ofId (CuspSubalgebra K) (Polynomial K)).comp f
  invFun := factorThroughCusp K
  left_inv f := AlgHom.ext fun _ => Subtype.ext rfl
  right_inv f := AlgHom.ext fun _ => rfl

end

end ManuscriptAudit.CuspUnramifiedNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspUnramifiedNormalization.image_mem_cusp,
      ``ManuscriptAudit.CuspUnramifiedNormalization.cuspSectionsEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
