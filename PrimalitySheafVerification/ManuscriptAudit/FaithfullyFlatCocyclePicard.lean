import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PicardGroup
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatTensorEqualizer

/-!
# Invertible modules from genuine faithfully flat unit cocycles

The two inverse twisted invariant modules pair into the untwisted
equalizer. The pairing becomes multiplication on split lines after
faithfully flat scalar extension, making it an isomorphism.
-/

namespace ManuscriptAudit.FaithfullyFlatCocyclePicard

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine
open FaithfullyFlatTensorEqualizer

universe u

noncomputable section


variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
variable (t : (Double A B)ˣ)

theorem inverse_isCocycle (ht : IsCocycle A B t) : IsCocycle A B t⁻¹ := by
  let f := Units.map (face02 A B).toMonoidHom
  let g := Units.map (face12 A B).toMonoidHom
  let h := Units.map (face01 A B).toMonoidHom
  have he : f t = g t * h t := Units.ext ht
  have hn : f t⁻¹ = g t⁻¹ * h t⁻¹ := by
    calc
      f t⁻¹ = (f t)⁻¹ := map_inv f t
      _ = (g t * h t)⁻¹ := congrArg Inv.inv he
      _ = (h t)⁻¹ * (g t)⁻¹ := mul_inv_rev _ _
      _ = (g t)⁻¹ * (h t)⁻¹ := mul_comm (h t)⁻¹ (g t)⁻¹
      _ = g t⁻¹ * h t⁻¹ := congrArg₂ (· * ·) (map_inv g t).symm (map_inv h t).symm
  exact congrArg Units.val hn

private theorem product_mem (x : invariants A B t) (y : invariants A B t⁻¹) :
    x.val * y.val ∈ invariants A B (1 : (Double A B)ˣ) := by
  have hx := (mem_invariants A B t _).1 x.property
  have hy := (mem_invariants A B t⁻¹ _).1 y.property
  apply (mem_invariants A B 1 _).2
  simp only [Units.val_one, one_mul, map_mul, hx, hy]
  calc
    ((t : Double A B) * first A B x.val) *
        ((↑(t⁻¹) : Double A B) * first A B y.val) =
        ((t : Double A B) * (↑(t⁻¹) : Double A B)) *
          (first A B x.val * first A B y.val) := by ac_rfl
    _ = first A B x.val * first A B y.val := by rw [Units.mul_inv, one_mul]

private def rawProduct : invariants A B t ⊗[A] invariants A B t⁻¹ →ₗ[A] B :=
  (multiplication A B).toLinearMap.comp
    (TensorProduct.map (invariants A B t).subtype (invariants A B t⁻¹).subtype)

private theorem rawProduct_tmul (x : invariants A B t) (y : invariants A B t⁻¹) :
    rawProduct A B t (x ⊗ₜ[A] y) = x.val * y.val := by
  change multiplication A B
    (TensorProduct.map (invariants A B t).subtype (invariants A B t⁻¹).subtype (x ⊗ₜ[A] y)) = _
  rw [TensorProduct.map_tmul, multiplication_tmul]
  rfl

private def productInvariant :
    invariants A B t ⊗[A] invariants A B t⁻¹ →ₗ[A] invariants A B (1 : (Double A B)ˣ) :=
  (rawProduct A B t).codRestrict _ fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (invariants A B (1 : (Double A B)ˣ)).zero_mem
    | tmul x y => rw [rawProduct_tmul]; exact product_mem A B t x y
    | add x y hx hy =>
      rw [map_add]
      exact (invariants A B (1 : (Double A B)ˣ)).add_mem hx hy

/-- Multiplication of inverse twisted invariants descends to the actual base ring. -/
def pairing : invariants A B t ⊗[A] invariants A B t⁻¹ →ₗ[A] A :=
  (baseEquiv A B).symm.toLinearMap.comp (productInvariant A B t)

theorem pairing_tmul (x : invariants A B t) (y : invariants A B t⁻¹) :
    algebraMap A B (pairing A B t (x ⊗ₜ[A] y)) = x.val * y.val := by
  rw [← baseEquiv_val A B]
  change ((baseEquiv A B) ((baseEquiv A B).symm (productInvariant A B t (x ⊗ₜ[A] y)))).val = _
  rw [LinearEquiv.apply_symm_apply]
  exact rawProduct_tmul A B t x y

private abbrev PairingDomain : Type u := invariants A B t ⊗[A] invariants A B t⁻¹

private def tensorPairing : B ⊗[A] PairingDomain A B t →ₗ[A] B ⊗[A] A :=
  (pairing A B t).lTensor B

private def tensorPairingEquiv (ht : IsCocycle A B t) :
    B ⊗[A] PairingDomain A B t ≃ₗ[A] B :=
  let L := invariants A B t
  let N := invariants A B t⁻¹
  let eL := (extensionEquiv A B t ht).restrictScalars A
  let eN := (extensionEquiv A B t⁻¹ (inverse_isCocycle A B t ht)).restrictScalars A
  (TensorProduct.assoc A B L N).symm.trans
    ((TensorProduct.congr eL (LinearEquiv.refl A N)).trans eN)

private theorem tensorPairing_formula (ht : IsCocycle A B t) :
    (TensorProduct.rid A B).toLinearMap.comp (tensorPairing A B t) =
      (tensorPairingEquiv A B t ht).toLinearMap := by
  apply TensorProduct.ext'
  intro b z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change (pairing A B t (x ⊗ₜ[A] y)) • b = (b * x.val) * y.val
    rw [Algebra.smul_def, pairing_tmul, mul_comm (x.val * y.val) b, mul_assoc]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem tensorPairing_bijective (ht : IsCocycle A B t) :
    Function.Bijective (tensorPairing A B t) := by
  let r := TensorProduct.rid A B
  let e := tensorPairingEquiv A B t ht
  have he : tensorPairing A B t = r.symm.toLinearMap.comp e.toLinearMap := by
    apply LinearMap.ext
    intro z
    apply r.injective
    exact (LinearMap.congr_fun (tensorPairing_formula A B t ht) z).trans
      (r.apply_symm_apply (e z)).symm
  rw [he]
  exact r.symm.bijective.comp e.bijective

private theorem tensorPairing_tmul (b : B) (v : PairingDomain A B t) :
    tensorPairing A B t (b ⊗ₜ[A] v) = b ⊗ₜ[A] pairing A B t v := rfl

private theorem pairing_injective (ht : IsCocycle A B t) :
    Function.Injective (pairing A B t) := by
  intro x y h
  have he : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y :=
    (tensorPairing_bijective A B t ht).1 (by
      rw [tensorPairing_tmul, tensorPairing_tmul, h])
  have hz : (1 : B) ⊗ₜ[A] (x - y) = 0 := by
    exact (TensorProduct.tmul_sub (R := A) (1 : B) x y).trans (sub_eq_zero.mpr he)
  exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := A) (M := PairingDomain A B t) (A := B) (m := x - y)).mp hz)

private theorem pairing_surjective (ht : IsCocycle A B t) :
    Function.Surjective (pairing A B t) := by
  let I : Ideal A := (pairing A B t).range
  let r := TensorProduct.rid A B
  have hMem (v : B ⊗[A] PairingDomain A B t) :
      r (tensorPairing A B t v) ∈ I • (⊤ : Submodule A B) := by
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact (I • (⊤ : Submodule A B)).zero_mem
    | tmul b x =>
      rw [tensorPairing_tmul]
      change pairing A B t x • b ∈ I • (⊤ : Submodule A B)
      exact Submodule.smul_mem_smul (show pairing A B t x ∈ I from ⟨x, rfl⟩) Submodule.mem_top
    | add x y hx hy =>
      rw [map_add, map_add]
      exact (I • (⊤ : Submodule A B)).add_mem hx hy
  have hTop : I • (⊤ : Submodule A B) = ⊤ := by
    apply eq_top_iff.mpr
    intro b _
    obtain ⟨v, hv⟩ := (tensorPairing_bijective A B t ht).2 (b ⊗ₜ[A] (1 : A))
    have h := hMem v
    rw [hv] at h
    change (1 : A) • b ∈ I • (⊤ : Submodule A B) at h
    simpa only [one_smul] using h
  have hI : I = ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A B).mp inferInstance).2 I hTop
  exact LinearMap.range_eq_top.mp hI

theorem pairing_bijective (ht : IsCocycle A B t) : Function.Bijective (pairing A B t) :=
  ⟨pairing_injective A B t ht, pairing_surjective A B t ht⟩

/-- A genuine faithfully flat unit cocycle determines an invertible module. -/
theorem invariants_invertible (ht : IsCocycle A B t) :
    Module.Invertible A (invariants A B t) :=
  Module.Invertible.left (LinearEquiv.ofBijective (pairing A B t) (pairing_bijective A B t ht))

end

end ManuscriptAudit.FaithfullyFlatCocyclePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatCocyclePicard.inverse_isCocycle,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.pairing_tmul,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.pairing_bijective,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.invariants_invertible] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
