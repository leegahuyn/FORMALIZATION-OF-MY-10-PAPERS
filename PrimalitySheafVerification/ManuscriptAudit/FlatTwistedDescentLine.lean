import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import PrimalitySheafVerification.ManuscriptAudit.TwistedTensorEqualizer

/-! Flat base change actually trivializes the invariant line of a
multiplicative tensor-square cocycle. -/

namespace ManuscriptAudit.FlatTwistedDescentLine

open Algebra TensorProduct
open TwistedTensorEqualizer

noncomputable section

set_option backward.defeqAttrib.useBackward true

universe u v

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
variable (t : (Double A B)ˣ)

private def multiply {C : Type*} [CommRing C] [Algebra A C] (c : C) : C →ₗ[A] C where
  toFun := fun x ↦ c * x
  map_add' _ _ := mul_add _ _ _
  map_smul' a x := by simp only [Algebra.smul_def, mul_left_comm, RingHom.id_apply]

/-- The actual linear difference of the two twisted descent maps. -/
def differential : B →ₗ[A] Double A B :=
  (second A B).toLinearMap - (multiply A (t : Double A B)).comp (first A B).toLinearMap

@[simp] theorem differential_apply (b : B) :
    differential A B t b = second A B b - (t : Double A B) * first A B b := rfl

/-- The genuine submodule of twisted invariant elements of the cover algebra. -/
def invariants : Submodule A B := LinearMap.ker (differential A B t)

theorem mem_invariants (b : B) :
    b ∈ invariants A B t ↔ second A B b = (t : Double A B) * first A B b := by
  change differential A B t b = 0 ↔ _
  rw [differential_apply, sub_eq_zero]

private def liftedDifferential : Double A B →ₗ[A] Triple A B :=
  (face02 A B).toLinearMap -
    (multiply A (face12 A B t)).comp (face01 A B).toLinearMap

private theorem liftedDifferential_apply (z : Double A B) :
    liftedDifferential A B t z = face02 A B z - face12 A B t * face01 A B z := rfl

private theorem differential_lTensor :
    (differential A B t).lTensor B = liftedDifferential A B t := by
  apply TensorProduct.ext'
  intro b c
  simp only [LinearMap.lTensor_tmul, differential_apply, liftedDifferential_apply,
    face02_tmul, face01_tmul, face12_apply, first_apply, second_apply, TensorProduct.tmul_sub,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Base change of the actual invariant-submodule inclusion. -/
def inclusion : B ⊗[A] invariants A B t →ₗ[A] Double A B :=
  (invariants A B t).subtype.lTensor B

private theorem kernel_exact : Function.Exact (invariants A B t).subtype (differential A B t) := by
  intro b
  constructor
  · intro hb
    exact ⟨⟨b, hb⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

variable [Module.Flat A B]

theorem inclusion_injective : Function.Injective (inclusion A B t) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := B) _ Subtype.val_injective

/-- Flatness identifies the range of the actual scalar-extended
invariant inclusion with the base-changed twisted equalizer. -/
theorem mem_range_inclusion (z : Double A B) :
    z ∈ Set.range (inclusion A B t) ↔ face02 A B z = face12 A B t * face01 A B z := by
  have h := Module.Flat.lTensor_exact B (kernel_exact A B t)
  change z ∈ Set.range ((invariants A B t).subtype.lTensor B) ↔ _
  rw [← h z, differential_lTensor, liftedDifferential_apply, sub_eq_zero]

/-- The actual normalization map on scalar-extended invariant line elements. -/
def extension : B ⊗[A] invariants A B t →ₗ[B] B :=
  AlgebraTensorModule.lift ((LinearMap.id : B →ₗ[B] B).smulRight (invariants A B t).subtype)

@[simp] theorem extension_tmul (b : B) (x : invariants A B t) :
    extension A B t (b ⊗ₜ[A] x) = b * x.val := rfl

private theorem extension_formula (z : B ⊗[A] invariants A B t) :
    extension A B t z = multiplication A B (inclusion A B t z) := by
  have h : (extension A B t).restrictScalars A =
      (multiplication A B).toLinearMap.comp (inclusion A B t) := by
    apply TensorProduct.ext'
    intro b x
    change extension A B t (b ⊗ₜ[A] x) = multiplication A B (inclusion A B t (b ⊗ₜ[A] x))
    simp only [extension_tmul, inclusion, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      multiplication_tmul]
  exact LinearMap.congr_fun h z

/-- The actual B-linear extension map is bijective. -/
theorem extension_bijective (ht : IsCocycle A B t) : Function.Bijective (extension A B t) := by
  have formula (x : B ⊗[A] invariants A B t) :
      inclusion A B t x = (t : Double A B) * first A B (extension A B t x) := by
    rw [extension_formula]
    apply (splitEqualizer_iff A B t ht _).mp
    exact (mem_range_inclusion A B t _).mp ⟨x, rfl⟩
  constructor
  · intro x y h
    apply inclusion_injective A B t
    exact (formula x).trans ((congrArg (fun b ↦ (t : Double A B) * first A B b) h).trans
      (formula y).symm)
  · intro b
    let z := (t : Double A B) * first A B b
    have hz : multiplication A B z = b := by simp [z, multiplication_cocycle A B t ht]
    have hc : z = (t : Double A B) * first A B (multiplication A B z) := by rw [hz]
    obtain ⟨x, hx⟩ := (mem_range_inclusion A B t z).mpr ((splitEqualizer_iff A B t ht z).mpr hc)
    exact ⟨x, (extension_formula A B t x).trans ((congrArg (multiplication A B) hx).trans hz)⟩

/-- Translation of the invariant line to its actual B-linear split
base change, using the real multiplication map. -/
def extensionEquiv (ht : IsCocycle A B t) :
    B ⊗[A] invariants A B t ≃ₗ[B] B :=
  LinearEquiv.ofBijective (extension A B t) (extension_bijective A B t ht)

end
end ManuscriptAudit.FlatTwistedDescentLine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FlatTwistedDescentLine.mem_invariants,
      ``ManuscriptAudit.FlatTwistedDescentLine.mem_range_inclusion,
      ``ManuscriptAudit.FlatTwistedDescentLine.extension_bijective,
      ``ManuscriptAudit.FlatTwistedDescentLine.extensionEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
