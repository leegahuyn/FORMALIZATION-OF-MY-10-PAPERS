import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedDescentLine

/-! Degree-zero faithfully flat descent in the literal tensor overlap. -/

namespace ManuscriptAudit.FaithfullyFlatTensorEqualizer

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine

noncomputable section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- The difference of the two canonical tensor inclusions has kernel precisely
the image of the base ring under the structure homomorphism. -/
theorem exact_algebraMap :
    Function.Exact (Algebra.linearMap A B) (differential A B (1 : (Double A B)ˣ)) := by
  have hL : (Algebra.linearMap A B).lTensor B =
      (first A B).toLinearMap.comp (TensorProduct.rid A B).toLinearMap := by
    apply TensorProduct.ext'
    intro b a
    change b ⊗ₜ[A] algebraMap A B a = (a • b) ⊗ₜ[A] (1 : B)
    rw [Algebra.algebraMap_eq_smul_one]
    exact (TensorProduct.smul_tmul a b (1 : B)).symm
  have hD : (differential A B (1 : (Double A B)ˣ)).lTensor B =
      (face02 A B).toLinearMap - (face01 A B).toLinearMap := by
    apply TensorProduct.ext'
    intro b c
    simp only [LinearMap.lTensor_tmul, differential_apply, Units.val_one, one_mul,
      TensorProduct.tmul_sub, LinearMap.sub_apply, AlgHom.toLinearMap_apply, face02_tmul, face01_tmul,
      first_apply, second_apply]
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).1
  rw [hL, hD]
  intro z
  change face02 A B z - face01 A B z = 0 ↔
    ∃ w, first A B (TensorProduct.rid A B w) = z
  rw [sub_eq_zero]
  have hCoc : IsCocycle A B (1 : (Double A B)ˣ) := by
    change face02 A B (1 : Double A B) = face12 A B 1 * face01 A B 1
    rw [map_one, map_one, map_one, mul_one]
  constructor
  · intro hz
    have hz' : z = first A B (multiplication A B z) := by
      simpa only [Units.val_one, one_mul] using
        (splitEqualizer_iff A B 1 hCoc z).1 (by simpa only [Units.val_one, map_one, one_mul] using hz)
    refine ⟨(TensorProduct.rid A B).symm (multiplication A B z), ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    exact hz'.symm
  · rintro ⟨w, rfl⟩
    simp

/-- The actual untwisted overlap-invariant line is the base ring. -/
def baseEquiv : A ≃ₗ[A] invariants A B (1 : (Double A B)ˣ) := by
  let f : A →ₗ[A] invariants A B (1 : (Double A B)ˣ) :=
    (Algebra.linearMap A B).codRestrict _ fun a => by
      apply (mem_invariants A B 1 _).2
      change second A B (algebraMap A B a) = (1 : Double A B) * first A B (algebraMap A B a)
      rw [one_mul, (second A B).commutes, (first A B).commutes]
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact FaithfulSMul.algebraMap_injective A B (congrArg Subtype.val hab)
  · intro z
    obtain ⟨a, ha⟩ := (exact_algebraMap A B z.val).1 z.property
    exact ⟨a, Subtype.ext ha⟩

theorem baseEquiv_val (a : A) :
    (baseEquiv A B a).val = algebraMap A B a := rfl

end

end ManuscriptAudit.FaithfullyFlatTensorEqualizer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatTensorEqualizer.exact_algebraMap,
      ``ManuscriptAudit.FaithfullyFlatTensorEqualizer.baseEquiv,
      ``ManuscriptAudit.FaithfullyFlatTensorEqualizer.baseEquiv_val] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
