import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Flat

/-!
# Function fields of integral affine étale charts

Base change from a domain to its fraction field gives the actual
generic fiber of an affine étale chart. For an integral chart it is
a finite étale domain over a field, hence a field. Its map from the
coordinate ring realizes that field as the chart's fraction field.
-/

namespace ManuscriptAudit.AffineEtaleGenericField

open Algebra.TensorProduct
open scoped nonZeroDivisors TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

variable (A B F : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Field F] [Algebra A B] [Algebra A F] [IsFractionRing A F] [Algebra.Etale A B]

private theorem baseMap_injective : Function.Injective (algebraMap A B) := by
  apply (injective_iff_map_eq_zero (algebraMap A B)).2
  intro a ha
  by_contra hn
  have hregular : IsRegular a :=
    isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
  have hr := Module.Flat.isSMulRegular_of_isRegular (M := B) hregular
  have h : a • (1 : B) = a • (0 : B) := by
    rw [← Algebra.algebraMap_eq_smul_one, ha, smul_zero]
  exact one_ne_zero (hr h)

private theorem mapped_nonZeroDivisors_le : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff (algebraMap A B) (baseMap_injective A B)).2
      (mem_nonZeroDivisors_iff_ne_zero.mp ha))

/-- The tensor-product generic fiber of an integral affine étale chart is a field. -/
theorem genericFiber_isField : IsField (F ⊗[A] B) := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (F ⊗[A] B) :=
    IsLocalization.tensorRight F A⁰
  letI : IsDomain (F ⊗[A] B) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ (mapped_nonZeroDivisors_le A B)
  letI : Module.Finite F (F ⊗[A] B) :=
    Algebra.FormallyUnramified.finite_of_free F (F ⊗[A] B)
  letI : IsArtinianRing (F ⊗[A] B) := IsArtinianRing.of_finite F _
  exact IsArtinianRing.isField_of_isDomain _

/-- The actual generic fiber is the fraction field of the chart's coordinate ring. -/
theorem genericFiber_isFractionRing : IsFractionRing B (F ⊗[A] B) := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (F ⊗[A] B) :=
    IsLocalization.tensorRight F A⁰
  have hh := mapped_nonZeroDivisors_le A B
  have hinj : Function.Injective (algebraMap B (F ⊗[A] B)) :=
    IsLocalization.injective _ hh
  letI : Field (F ⊗[A] B) := (genericFiber_isField A B F).toField
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ hh
  intro b hb
  exact isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff (algebraMap B (F ⊗[A] B)) hinj).2
      (mem_nonZeroDivisors_iff_ne_zero.mp hb))

end

end ManuscriptAudit.AffineEtaleGenericField

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleGenericField.genericFiber_isField,
      ``ManuscriptAudit.AffineEtaleGenericField.genericFiber_isFractionRing] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
