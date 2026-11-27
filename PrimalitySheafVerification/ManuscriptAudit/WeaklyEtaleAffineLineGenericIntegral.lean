import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.TorsionFree
import PrimalitySheafVerification.ManuscriptAudit.ReducedFiberDenominatorCancellation
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres

/-! Weakly étale affine algebras on the affine line are relatively
integrally closed in their genuine generic localization. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineGenericIntegral

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open ReducedFiberDenominatorCancellation (exists_of_integral_of_denominator)
open WeaklyEtaleAffineLineReducedFibres (reduced_prime_fibre)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

abbrev denominators : Submonoid B := Algebra.algebraMapSubmonoid B (R K)⁰
abbrev genericRing := Localization (denominators K B)

private theorem denominator_nonzerodivisor : denominators K B ≤ B⁰ := by
  let φ := CommRingCat.ofHom (algebraMap (R K) B)
  letI : Module.Flat (R K) B := (RingHom.flat_algebraMap_iff).mp
    ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat (structureMap (R K) B))))
  rintro z ⟨a, ha, rfl⟩
  have h : IsSMulRegular B a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  have hm : Function.Injective (fun b : B ↦ algebraMap (R K) B a * b) := by
    simpa only [Algebra.smul_def] using h
  apply isRegular_iff_mem_nonZeroDivisors.mp
  exact ⟨hm, fun _ _ e ↦ hm (by simpa only [mul_comm] using e)⟩

set_option maxHeartbeats 1000000 in
/-- Every element of the literal generic localization integral over the
actual weakly étale chart already lies on the chart. -/
theorem exists_of_integral (x : genericRing K B) (hx : IsIntegral B x) :
    ∃ b : B, algebraMap B (genericRing K B) b = x := by
  let L := genericRing K B
  let S := denominators K B
  have hB : Function.Injective (algebraMap B L) :=
    IsLocalization.injective L (denominator_nonzerodivisor K B)
  have hUnit (a : R K) (ha : a ≠ 0) :
      IsUnit (algebraMap B L (algebraMap (R K) B a)) :=
    IsLocalization.map_units L
      (⟨algebraMap (R K) B a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩⟩ : S)
  obtain ⟨⟨b, d⟩, hb⟩ := IsLocalization.surj S x
  obtain ⟨a, ha, hd⟩ := d.property
  apply exists_of_integral_of_denominator hB hUnit (reduced_prime_fibre K B) hx
    (nonZeroDivisors.ne_zero ha) b
  calc
    _ = x * algebraMap B L (d : B) := hb.symm
    _ = algebraMap B L (algebraMap (R K) B a) * x := by rw [hd, mul_comm]

end
end ManuscriptAudit.WeaklyEtaleAffineLineGenericIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineGenericIntegral.exists_of_integral
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
