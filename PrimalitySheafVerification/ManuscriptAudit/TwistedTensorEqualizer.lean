import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps

/-! The actual twisted Čech equalizer becomes split after tensoring
with the cover algebra. -/

namespace ManuscriptAudit.TwistedTensorEqualizer

open Algebra TensorProduct

noncomputable section

universe u v

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]

abbrev Double := B ⊗[A] B
abbrev Triple := B ⊗[A] Double A B

/-- First map into the actual tensor square. -/
def first : B →ₐ[A] Double A B :=
  Algebra.TensorProduct.includeLeft

/-- Second map into the actual tensor square. -/
def second : B →ₐ[A] Double A B :=
  Algebra.TensorProduct.includeRight

/-- The diagonal multiplication on the tensor square. -/
def multiplication : Double A B →ₐ[A] B := Algebra.TensorProduct.lmul' A

/-- The (0,1) face map into the tensor cube. -/
def face01 : Double A B →ₐ[A] Triple A B :=
  Algebra.TensorProduct.map (AlgHom.id A B) (first A B)

/-- The (0,2) face map into the tensor cube. -/
def face02 : Double A B →ₐ[A] Triple A B :=
  Algebra.TensorProduct.map (AlgHom.id A B) (second A B)

/-- The (1,2) face map into the tensor cube. -/
def face12 : Double A B →ₐ[A] Triple A B :=
  Algebra.TensorProduct.includeRight

/-- Multiply the first two input factors and retain the third factor. -/
def contraction : Triple A B →ₐ[A] Double A B :=
  Algebra.TensorProduct.lift (first A B) (AlgHom.id A (Double A B)) (fun x y ↦ Commute.all _ _)

@[simp] theorem first_apply (b : B) : first A B b = b ⊗ₜ[A] 1 := rfl
@[simp] theorem second_apply (b : B) : second A B b = 1 ⊗ₜ[A] b := rfl

@[simp] theorem multiplication_tmul (b c : B) :
    multiplication A B (b ⊗ₜ[A] c) = b * c := Algebra.TensorProduct.lmul'_apply_tmul b c

@[simp] theorem face01_tmul (b c : B) :
    face01 A B (b ⊗ₜ[A] c) = b ⊗ₜ[A] (c ⊗ₜ[A] 1) := by
  rw [face01, Algebra.TensorProduct.map_tmul] <;> rfl

@[simp] theorem face02_tmul (b c : B) :
    face02 A B (b ⊗ₜ[A] c) = b ⊗ₜ[A] (1 ⊗ₜ[A] c) := by
  rw [face02, Algebra.TensorProduct.map_tmul] <;> rfl

@[simp] theorem face12_apply (z : Double A B) : face12 A B z = 1 ⊗ₜ[A] z := rfl

@[simp] theorem contraction_tmul (b c d : B) :
    contraction A B (b ⊗ₜ[A] (c ⊗ₜ[A] d)) = (b * c) ⊗ₜ[A] d := by
  unfold contraction
  rw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem contraction_face01 (z : Double A B) :
    contraction A B (face01 A B z) = first A B (multiplication A B z) := by
  have h : (contraction A B).comp (face01 A B) = (first A B).comp (multiplication A B) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro b c
    change contraction A B (face01 A B (b ⊗ₜ[A] c)) =
      first A B (multiplication A B (b ⊗ₜ[A] c))
    simp
  exact AlgHom.congr_fun h z

private theorem contraction_face02 (z : Double A B) :
    contraction A B (face02 A B z) = z := by
  have h : (contraction A B).comp (face02 A B) = AlgHom.id A (Double A B) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro b c
    change contraction A B (face02 A B (b ⊗ₜ[A] c)) = b ⊗ₜ[A] c
    simp
  exact AlgHom.congr_fun h z

private theorem contraction_face12 (z : Double A B) :
    contraction A B (face12 A B z) = z := by
  rw [face12_apply, contraction, Algebra.TensorProduct.lift_tmul, map_one, one_mul] <;> rfl

private theorem faces_on_first (b : B) :
    face02 A B (first A B b) = face01 A B (first A B b) := by simp

/-- Actual Čech multiplicative cocycle equation for the three tensor faces. -/
def IsCocycle (u : (Double A B)ˣ) : Prop :=
  face02 A B u = face12 A B u * face01 A B u

/-- A tensor in the base-changed twisted equalizer is determined by
its multiplication, with an explicit inverse formula. -/
theorem splitEqualizer_iff (u : (Double A B)ˣ) (hu : IsCocycle A B u) (z : Double A B) :
    face02 A B z = face12 A B u * face01 A B z ↔
      z = (u : Double A B) * first A B (multiplication A B z) := by
  constructor
  · intro h
    have h' := congrArg (contraction A B) h
    rwa [map_mul, contraction_face01, contraction_face02, contraction_face12] at h'
  · intro hz
    have hc : face02 A B u = face12 A B u * face01 A B u := hu
    rw [hz]
    simp only [map_mul]
    rw [hc, faces_on_first, mul_assoc]

/-- The actual diagonal restriction of a unit cocycle is the identity. -/
theorem multiplication_cocycle (u : (Double A B)ˣ) (hu : IsCocycle A B u) :
    multiplication A B (u : Double A B) = 1 := by
  have h := (splitEqualizer_iff A B u hu (u : Double A B)).mp hu
  have hz : first A B (multiplication A B (u : Double A B)) = 1 := by
    apply u.isUnit.mul_left_cancel
    rw [mul_one]
    exact h.symm
  have h' := congrArg (multiplication A B) hz
  simpa using h'

end
end ManuscriptAudit.TwistedTensorEqualizer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TwistedTensorEqualizer.splitEqualizer_iff,
      ``ManuscriptAudit.TwistedTensorEqualizer.multiplication_cocycle] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
