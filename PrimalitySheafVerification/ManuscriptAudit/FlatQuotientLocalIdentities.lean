import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! The kernel of a surjective flat algebra map has local multiplicative identities. -/

namespace ManuscriptAudit.FlatQuotientLocalIdentities

open scoped TensorProduct
open TensorProduct

noncomputable section

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]

theorem exists_kernel_left_identity
    (surj : Function.Surjective (algebraMap R B)) {x : R}
    (hx : algebraMap R B x = 0) :
    ∃ e : R, algebraMap R B e = 0 ∧ e * x = x := by
  let m : R →ₗ[R] R := {
    toFun := fun r => x * r
    map_add' := fun a b => mul_add x a b
    map_smul' := fun a b => by simp [smul_eq_mul, mul_left_comm] }
  let K := LinearMap.ker m
  have hExact : Function.Exact K.subtype m := by
    intro r
    constructor
    · intro hr
      exact ⟨⟨r, hr⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.property
  have hTensor := Module.Flat.rTensor_exact (M := B) hExact
  let unitPair : R ⊗[R] B := (1 : R) ⊗ₜ[R] (1 : B)
  let collapse := TensorProduct.lid R B
  have hZero : (m.rTensor B) unitPair = 0 := by
    apply collapse.injective
    change collapse ((m.rTensor B) ((1 : R) ⊗ₜ[R] (1 : B))) = collapse 0
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero]
    change (x * (1 : R)) • (1 : B) = 0
    rw [mul_one, Algebra.smul_def, hx, zero_mul]
  obtain ⟨z, hz⟩ := (hTensor unitPair).mp hZero
  have hLift (w : K ⊗[R] B) :
      ∃ y : K, algebraMap R B (y : R) = collapse ((K.subtype.rTensor B) w) := by
    induction w using TensorProduct.induction_on with
    | zero =>
      exact ⟨0, by simp [collapse]⟩
    | tmul k b =>
      obtain ⟨r, rfl⟩ := surj b
      refine ⟨r • k, ?_⟩
      change algebraMap R B (r * (k : R)) =
        (TensorProduct.lid R B) ((K.subtype.rTensor B) (k ⊗ₜ[R] algebraMap R B r))
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.smul_def, map_mul, mul_comm] <;> rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a+b, by
        change algebraMap R B ((a : R) + (b : R)) =
          collapse ((K.subtype.rTensor B) (u+v))
        simp only [map_add, ha, hb]⟩
  obtain ⟨y, hy⟩ := hLift z
  have hOne : algebraMap R B (y : R) = 1 := by
    rw [hy, hz]
    simp [collapse, unitPair]
  have hAnnihilate : x * (y : R) = 0 := y.property
  refine ⟨1-(y : R), by simp [map_sub, hOne], ?_⟩
  rw [sub_mul, one_mul, mul_comm (y : R) x, hAnnihilate, sub_zero]

end
end ManuscriptAudit.FlatQuotientLocalIdentities

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatQuotientLocalIdentities.exists_kernel_left_identity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
