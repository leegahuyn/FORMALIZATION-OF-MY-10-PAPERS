import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary

/-! Refining a faithfully flat affine cover preserves its descended line. -/

namespace ManuscriptAudit.FaithfullyFlatCocycleRefinement

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine
open FaithfullyFlatCocyclePicard

noncomputable section

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (f : B →ₐ[A] C)

private abbrev doubleMap : Double A B →ₐ[A] Double A C := Algebra.TensorProduct.map f f
private abbrev tripleMap : Triple A B →ₐ[A] Triple A C :=
  Algebra.TensorProduct.map f (doubleMap A B C f)

/-- Pull an actual tensor-overlap unit to the refined cover. -/
def pull (t : (Double A B)ˣ) : (Double A C)ˣ :=
  Units.map (doubleMap A B C f).toMonoidHom t

private theorem face01_natural (z : Double A B) :
    tripleMap A B C f (face01 A B z) = face01 A C (doubleMap A B C f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem face02_natural (z : Double A B) :
    tripleMap A B C f (face02 A B z) = face02 A C (doubleMap A B C f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pull_isCocycle (t : (Double A B)ˣ) (ht : IsCocycle A B t) :
    IsCocycle A C (pull A B C f t) := by
  change face02 A C (doubleMap A B C f t) =
    face12 A C (doubleMap A B C f t) * face01 A C (doubleMap A B C f t)
  have h := congrArg (tripleMap A B C f) ht
  rw [map_mul, face02_natural, face01_natural] at h
  simpa only [face12_apply, Algebra.TensorProduct.map_tmul, map_one] using h

/-- The map of algebras sends actual twisted invariants to twisted invariants on the refinement. -/
def mapInvariants (t : (Double A B)ˣ) :
    invariants A B t →ₗ[A] invariants A C (pull A B C f t) :=
  (f.toLinearMap.comp (invariants A B t).subtype).codRestrict _ fun x => by
    apply (mem_invariants A C _ _).2
    have h := congrArg (doubleMap A B C f) ((mem_invariants A B t _).1 x.property)
    change second A C (f x.val) =
      doubleMap A B C f t * first A C (f x.val)
    simpa only [first_apply, second_apply, map_mul, map_one, Algebra.TensorProduct.map_tmul] using h

variable [Module.FaithfullyFlat A B] [Module.FaithfullyFlat A C]
variable (t : (Double A B)ˣ) (ht : IsCocycle A B t)

/-- If both covers are faithfully flat, refinement induces an actual
linear equivalence of the descended modules. -/
def refinementEquiv : invariants A B t ≃ₗ[A] invariants A C (pull A B C f t) := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let L := invariants A B t
  let L' := invariants A C (pull A B C f t)
  let eB := extensionEquiv A B t ht
  let eC := extensionEquiv A C (pull A B C f t) (pull_isCocycle A B C f t ht)
  let D : C ⊗[A] L ≃ₗ[C] C :=
    (AlgebraTensorModule.cancelBaseChange A B C C L).symm.trans
      ((eB.baseChange B C (B ⊗[A] L) B).trans (AlgebraTensorModule.rid B C C))
  let g : L →ₗ[A] L' := mapInvariants A B C f t
  let k := g.lTensor C
  let e := eC.restrictScalars A
  let d := D.restrictScalars A
  have hMap : e.toLinearMap.comp k = d.toLinearMap := by
    apply TensorProduct.ext'
    intro c x
    change c * f x.val = (eB ((1 : B) ⊗ₜ[A] x)) • c
    change c * f x.val = (extension A B t ((1 : B) ⊗ₜ[A] x)) • c
    rw [extension_tmul, one_mul, Algebra.smul_def]
    change c * f x.val = f x.val * c
    exact mul_comm _ _
  have hk : Function.Bijective k := by
    have h : k = e.symm.toLinearMap.comp d.toLinearMap := by
      apply LinearMap.ext
      intro z
      apply e.injective
      exact (LinearMap.congr_fun hMap z).trans (e.apply_symm_apply (d z)).symm
    rw [h]
    exact e.symm.bijective.comp d.bijective
  exact LinearEquiv.ofBijective g
    ((Module.FaithfullyFlat.lTensor_bijective_iff_bijective A C g).1 hk)

/-- The genuine descended Picard class is independent of a faithfully flat refinement. -/
theorem picardClass_eq_pull :
    picardClass A B t ht =
      picardClass A C (pull A B C f t) (pull_isCocycle A B C f t ht) := by
  letI := invariants_invertible A B t ht
  letI := invariants_invertible A C (pull A B C f t) (pull_isCocycle A B C f t ht)
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨refinementEquiv A B C f t ht⟩

end

end ManuscriptAudit.FaithfullyFlatCocycleRefinement

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatCocycleRefinement.pull_isCocycle,
      ``ManuscriptAudit.FaithfullyFlatCocycleRefinement.refinementEquiv,
      ``ManuscriptAudit.FaithfullyFlatCocycleRefinement.picardClass_eq_pull] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
