import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary

/-! Multiplication of overlap unit cocycles corresponds to tensor
product in the actual affine Picard group. -/

namespace ManuscriptAudit.FaithfullyFlatCocycleProduct

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine
open FaithfullyFlatCocyclePicard

universe u

noncomputable section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (t s : (Double A B)ˣ)

theorem mul_isCocycle (ht : IsCocycle A B t) (hs : IsCocycle A B s) :
    IsCocycle A B (t * s) := by
  change face02 A B (t : Double A B) = _ at ht
  change face02 A B (s : Double A B) = _ at hs
  change face02 A B ((t : Double A B) * (s : Double A B)) =
    face12 A B ((t : Double A B) * (s : Double A B)) *
      face01 A B ((t : Double A B) * (s : Double A B))
  simp only [map_mul, ht, hs]
  ac_rfl

private theorem mul_mem (x : invariants A B t) (y : invariants A B s) :
    x.val * y.val ∈ invariants A B (t * s) := by
  have hx := (mem_invariants A B t _).1 x.property
  have hy := (mem_invariants A B s _).1 y.property
  apply (mem_invariants A B (t * s) _).2
  simp only [Units.val_mul, map_mul, hx, hy]
  ac_rfl

private def rawProduct : invariants A B t ⊗[A] invariants A B s →ₗ[A] B :=
  (multiplication A B).toLinearMap.comp
    (TensorProduct.map (invariants A B t).subtype (invariants A B s).subtype)

private theorem rawProduct_tmul (x : invariants A B t) (y : invariants A B s) :
    rawProduct A B t s (x ⊗ₜ[A] y) = x.val * y.val := by
  change multiplication A B
    (TensorProduct.map (invariants A B t).subtype (invariants A B s).subtype (x ⊗ₜ[A] y)) = _
  rw [TensorProduct.map_tmul, multiplication_tmul] <;> rfl

/-- Multiplication of two twisted invariant elements gives a twisted invariant
for the product of their cocycles. -/
def productMap : invariants A B t ⊗[A] invariants A B s →ₗ[A] invariants A B (t * s) :=
  (rawProduct A B t s).codRestrict _ fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (invariants A B (t * s)).zero_mem
    | tmul x y => rw [rawProduct_tmul]; exact mul_mem A B t s x y
    | add x y hx hy =>
      rw [map_add]
      exact (invariants A B (t * s)).add_mem hx hy

variable [Module.FaithfullyFlat A B]
variable (ht : IsCocycle A B t) (hs : IsCocycle A B s)

/-- This multiplication map is an isomorphism of descended modules, as
can be checked after the genuinely faithfully flat extension. -/
def productEquiv :
    invariants A B t ⊗[A] invariants A B s ≃ₗ[A] invariants A B (t * s) := by
  let L := invariants A B t
  let N := invariants A B s
  let eL := (extensionEquiv A B t ht).restrictScalars A
  let eN := (extensionEquiv A B s hs).restrictScalars A
  let d : B ⊗[A] (L ⊗[A] N) ≃ₗ[A] B :=
    (TensorProduct.assoc A B L N).symm.trans
      ((TensorProduct.congr eL (LinearEquiv.refl A N)).trans eN)
  let e := (extensionEquiv A B (t * s) (mul_isCocycle A B t s ht hs)).restrictScalars A
  let g := productMap A B t s
  let f := g.lTensor B
  have hMap : e.toLinearMap.comp f = d.toLinearMap := by
    apply TensorProduct.ext'
    intro b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      change b * rawProduct A B t s (x ⊗ₜ[A] y) = (b * x.val) * y.val
      rw [rawProduct_tmul, mul_assoc]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  have hf : Function.Bijective f := by
    have h : f = e.symm.toLinearMap.comp d.toLinearMap := by
      apply LinearMap.ext
      intro z
      apply e.injective
      exact (LinearMap.congr_fun hMap z).trans (e.apply_symm_apply (d z)).symm
    rw [h]
    exact e.symm.bijective.comp d.bijective
  exact LinearEquiv.ofBijective g
    ((Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g).1 hf)

theorem picardClass_mul :
    picardClass A B (t * s) (mul_isCocycle A B t s ht hs) =
      picardClass A B t ht * picardClass A B s hs := by
  letI := invariants_invertible A B t ht
  letI := invariants_invertible A B s hs
  letI := invariants_invertible A B (t * s) (mul_isCocycle A B t s ht hs)
  change CommRing.Pic.mk A (invariants A B (t * s)) =
    CommRing.Pic.mk A (invariants A B t) * CommRing.Pic.mk A (invariants A B s)
  rw [← CommRing.Pic.mk_tensor]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨(productEquiv A B t s ht hs).symm⟩

end

end ManuscriptAudit.FaithfullyFlatCocycleProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatCocycleProduct.mul_isCocycle,
      ``ManuscriptAudit.FaithfullyFlatCocycleProduct.productEquiv,
      ``ManuscriptAudit.FaithfullyFlatCocycleProduct.picardClass_mul] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
