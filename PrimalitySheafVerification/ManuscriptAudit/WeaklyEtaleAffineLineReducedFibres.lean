import Lean.Util.CollectAxioms
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.TensorProduct.Quotient
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk

/-! Every actual principal closed fibre of a weakly étale affine chart
over the affine line over an algebraically closed field is reduced. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open ProetaleAffineTensor (structureMap specMap leftInclusion specTensor_isPullback)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

theorem reduced_over_algebraicallyClosed {K B : Type u} [Field K] [IsAlgClosed K]
    [CommRing B] (f : ProetaleAffineTensor.spectrum B ⟶ ProetaleAffineTensor.spectrum K) [WeaklyEtale f] : IsReduced B := by
  apply isReduced_ofLocalizationMaximal
  intro J hJ
  letI : J.IsPrime := hJ.isPrime
  let R := Localization.AtPrime J
  have hR : IsField R :=
    WeaklyEtaleAlgebraicallyClosedStalk.localRing_isField K f ⟨J, hJ.isPrime⟩
  letI : Field R := hR.toField
  exact inferInstanceAs (IsReduced R)

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]

private abbrev R := Polynomial K

private theorem exists_point_ideal {p : R K} (hp : Prime p) :
    ∃ a : K, Ideal.span ({p} : Set (R K)) = Ideal.span ({X - C a} : Set (R K)) := by
  have hd : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp.irreducible]
    exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hd
  have hassoc : Associated (X - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp.irreducible ((dvd_iff_isRoot).mpr ha)
  exact ⟨a, Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm⟩

variable [WeaklyEtale (structureMap (R K) B)]

set_option maxHeartbeats 1500000 in
/-- The literal quotient by a prime affine-line parameter is reduced. -/
theorem reduced_prime_fibre (p : R K) (hp : Prime p) :
    IsReduced (B ⧸ Ideal.span ({algebraMap (R K) B p} : Set B)) := by
  let I := Ideal.span ({p} : Set (R K))
  letI : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let F := R K ⧸ I
  letI : Field F := Ideal.Quotient.field I
  obtain ⟨a, ha⟩ := exists_point_ideal K hp
  let eF : F ≃ₐ[K] K :=
    (Ideal.quotientEquivAlgOfEq K ha).trans (quotientSpanXSubCAlgEquiv a)
  letI : IsAlgClosed F := IsAlgClosed.of_ringEquiv K F eF.symm.toRingEquiv
  let S := F ⊗[R K] B
  let f : ProetaleAffineTensor.spectrum S ⟶ ProetaleAffineTensor.spectrum F := specMap (R K) (leftInclusion (R K) F B)
  have hf : WeaklyEtale (structureMap (R K) B) := inferInstance
  letI : WeaklyEtale f := MorphismProperty.of_isPullback (P := @WeaklyEtale)
    (specTensor_isPullback (R K) F B).flip hf
  letI : IsReduced S := reduced_over_algebraicallyClosed f
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hI : I.map (algebraMap (R K) B) = Ideal.span ({algebraMap (R K) B p} : Set B) := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  rw [← hI]
  exact isReduced_of_injective e e.injective

end
end ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres.reduced_over_algebraicallyClosed,
      ``ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres.reduced_prime_fibre] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
