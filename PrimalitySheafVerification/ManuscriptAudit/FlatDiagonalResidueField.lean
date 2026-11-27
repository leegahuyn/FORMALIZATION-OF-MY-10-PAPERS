import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import PrimalitySheafVerification.ManuscriptAudit.FlatDiagonalPolynomial

/-! A local algebra with flat diagonal has algebraic residue field. -/

namespace ManuscriptAudit.FlatDiagonalResidueField

noncomputable section

universe u v

variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [IsLocalRing B]

/-- If the actual tensor multiplication of a local algebra is flat, its
residue field is algebraic over the base field. -/
theorem isAlgebraic_residueField
    (hμ : (Algebra.TensorProduct.lmul' (S := B) K).Flat) :
    Algebra.IsAlgebraic K (IsLocalRing.ResidueField B) := by
  constructor
  intro x
  by_contra hx
  have ht := transcendental_iff.mp (show Transcendental K x from hx)
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective x
  let φ : Polynomial K →ₐ[K] B := Polynomial.aeval b
  let q : B →ₐ[K] IsLocalRing.ResidueField B := IsScalarTower.toAlgHom K B _
  have hq (p : Polynomial K) : IsLocalRing.residue B (φ p) = Polynomial.aeval x p := by
    change q (Polynomial.aeval b p) = Polynomial.aeval x p
    rw [← Polynomial.aeval_algHom_apply q b p]
    change Polynomial.aeval (IsLocalRing.residue B b) p = _
    rw [hb]
  have hunit (p : Polynomial K) (hp : p ≠ 0) : IsUnit (φ p) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (φ p)).mp (fun hz ↦ hp (ht p ((hq p).symm.trans hz)))
  letI : Algebra (Polynomial K) B := φ.toRingHom.toAlgebra
  letI : Module.IsTorsionFree (Polynomial K) B :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun p y h ↦ by
      by_cases hp : p = 0
      · exact Or.inl hp
      · right
        change φ p * y = 0 at h
        exact (hunit p hp).mul_left_cancel (h.trans (mul_zero (φ p)).symm)
  exact FlatDiagonalPolynomial.not_flat_polynomial_parameter K B φ hμ
    (inferInstanceAs (Module.Flat (Polynomial K) B))

/-- Over an algebraically closed base field, the native residue field of
a local algebra with flat diagonal is the base field. -/
def residueFieldEquiv [IsAlgClosed K]
    (hμ : (Algebra.TensorProduct.lmul' (S := B) K).Flat) :
    K ≃ₐ[K] IsLocalRing.ResidueField B := by
  letI := isAlgebraic_residueField K B hμ
  exact AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral

end
end ManuscriptAudit.FlatDiagonalResidueField

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FlatDiagonalResidueField.isAlgebraic_residueField,
      ``ManuscriptAudit.FlatDiagonalResidueField.residueFieldEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
