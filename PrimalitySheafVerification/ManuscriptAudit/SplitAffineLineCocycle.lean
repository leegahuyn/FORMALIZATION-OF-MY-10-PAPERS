import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary

/-!
# The actual unit cocycle of a split affine line

A chosen trivialization on a faithfully flat algebra compares after the
two tensor-square pullbacks by a unit. The triple identities and the
faithfully flat comparison recover the original module.
-/

namespace ManuscriptAudit.SplitAffineLineCocycle

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine

noncomputable section

variable (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M]
variable (e : B ⊗[A] M ≃ₗ[B] B)

section Extension

variable {C : Type*} [CommRing C] [Algebra A C]

/-- Extend the actual chosen trivialization along a map of cover algebras. -/
def extend (f : B →ₐ[A] C) : C ⊗[A] M ≃ₗ[C] C := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algHom f
  exact (AlgebraTensorModule.cancelBaseChange A B C C M).symm.trans
    ((e.baseChange B C (B ⊗[A] M) B).trans (AlgebraTensorModule.rid B C C))

@[simp] theorem extend_tmul (f : B →ₐ[A] C) (c : C) (m : M) :
    extend A B M e f (c ⊗ₜ[A] m) = c * f (e ((1 : B) ⊗ₜ[A] m)) := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algHom f
  change e ((1 : B) ⊗ₜ[A] m) • c = _
  rw [Algebra.smul_def]
  change f (e ((1 : B) ⊗ₜ[A] m)) * c = _
  exact mul_comm _ _

end Extension

private abbrev comparison : Double A B ≃ₗ[Double A B] Double A B :=
  (extend A B M e (first A B)).symm.trans (extend A B M e (second A B))

private theorem comparison_apply (b : Double A B) :
    comparison A B M e b = b * comparison A B M e 1 := by
  simpa only [smul_eq_mul, mul_one] using (comparison A B M e).map_smul b (1 : Double A B)

/-- The actual transition unit between the two tensor-square trivializations. -/
def transitionUnit : (Double A B)ˣ := by
  let T := comparison A B M e
  have h : T.symm 1 * T 1 = 1 :=
    (comparison_apply A B M e (T.symm 1)).symm.trans (T.apply_symm_apply 1)
  exact ⟨T 1, T.symm 1, (mul_comm _ _).trans h, h⟩

private theorem transition_apply (m : M) :
    second A B (e ((1 : B) ⊗ₜ[A] m)) =
      (transitionUnit A B M e : Double A B) * first A B (e ((1 : B) ⊗ₜ[A] m)) := by
  let z := (1 : Double A B) ⊗ₜ[A] m
  have h := comparison_apply A B M e (extend A B M e (first A B) z)
  change (extend A B M e (second A B)) ((extend A B M e (first A B)).symm
    (extend A B M e (first A B) z)) =
      extend A B M e (first A B) z * (transitionUnit A B M e : Double A B) at h
  rw [LinearEquiv.symm_apply_apply] at h
  change extend A B M e (second A B) ((1 : Double A B) ⊗ₜ[A] m) =
    extend A B M e (first A B) ((1 : Double A B) ⊗ₜ[A] m) * (transitionUnit A B M e : Double A B) at h
  rw [extend_tmul, extend_tmul, one_mul, one_mul, mul_comm] at h
  exact h

private theorem transition_extend {C : Type*} [CommRing C] [Algebra A C]
    (f : Double A B →ₐ[A] C) (z : C ⊗[A] M) :
    extend A B M e (f.comp (second A B)) z =
      f (transitionUnit A B M e : Double A B) * extend A B M e (f.comp (first A B)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
    simp only [extend_tmul, AlgHom.comp_apply, transition_apply, map_mul]
    ac_rfl
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

/-- The actual transition unit satisfies the triple overlap identity. -/
theorem transitionUnit_isCocycle : IsCocycle A B (transitionUnit A B M e) := by
  let α := (face01 A B).comp (first A B)
  let β := (face01 A B).comp (second A B)
  let γ := (face12 A B).comp (second A B)
  have hα : (face02 A B).comp (first A B) = α := by
    apply AlgHom.ext
    intro b
    change face02 A B (first A B b) = face01 A B (first A B b)
    simp
  have hβ : (face12 A B).comp (first A B) = β := by
    apply AlgHom.ext
    intro b
    change face12 A B (first A B b) = face01 A B (second A B b)
    simp
  have hγ : (face02 A B).comp (second A B) = γ := by
    apply AlgHom.ext
    intro b
    change face02 A B (second A B b) = face12 A B (second A B b)
    simp
  let z := (extend A B M e α).symm 1
  have h1 : extend A B M e α z = 1 := (extend A B M e α).apply_symm_apply _
  have h12 := transition_extend A B M e (face01 A B) z
  change extend A B M e β z =
    face01 A B (transitionUnit A B M e : Double A B) * extend A B M e α z at h12
  rw [h1, mul_one] at h12
  have h23 := transition_extend A B M e (face12 A B) z
  rw [hβ, h12] at h23
  have h13 := transition_extend A B M e (face02 A B) z
  rw [hα, hγ, h1, mul_one] at h13
  exact h13.symm.trans h23

private def normalizer : M →ₗ[A] B :=
  (e.restrictScalars A).toLinearMap.comp (TensorProduct.mk A B M 1)

/-- The original module maps to the actual invariants of its transition unit. -/
def toInvariants : M →ₗ[A] invariants A B (transitionUnit A B M e) :=
  (normalizer A B M e).codRestrict _ fun m =>
    (mem_invariants A B (transitionUnit A B M e) _).2 (transition_apply A B M e m)

variable [Module.FaithfullyFlat A B]

/-- The original module is recovered from invariants of its true transition cocycle. -/
def invariantsEquiv : M ≃ₗ[A] invariants A B (transitionUnit A B M e) := by
  let t := transitionUnit A B M e
  let L := invariants A B t
  let f : M →ₗ[A] L := toInvariants A B M e
  let E := (extensionEquiv A B t (transitionUnit_isCocycle A B M e)).restrictScalars A
  let u := e.restrictScalars A
  have hMap : E.toLinearMap.comp (f.lTensor B) = u.toLinearMap := by
    apply TensorProduct.ext'
    intro b m
    change b * e ((1 : B) ⊗ₜ[A] m) = e (b ⊗ₜ[A] m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (e.map_smul b ((1 : B) ⊗ₜ[A] m)).symm
  have hLift : f.lTensor B = E.symm.toLinearMap.comp u.toLinearMap := by
    apply LinearMap.ext
    intro z
    apply E.injective
    exact (LinearMap.congr_fun hMap z).trans (E.apply_symm_apply (u z)).symm
  have hBij : Function.Bijective (f.lTensor B) := by
    rw [hLift]
    exact E.symm.bijective.comp u.bijective
  exact LinearEquiv.ofBijective f
    ((Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B f).1 hBij)

end

end ManuscriptAudit.SplitAffineLineCocycle

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SplitAffineLineCocycle.transitionUnit_isCocycle,
      ``ManuscriptAudit.SplitAffineLineCocycle.invariantsEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
