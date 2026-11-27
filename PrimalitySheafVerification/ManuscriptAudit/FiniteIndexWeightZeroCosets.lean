import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.GroupTheory.Index

/-! A finite product over right cosets for a weight-zero invariant function. -/

namespace ManuscriptAudit.FiniteIndexWeightZeroCosets

open Set UpperHalfPlane
open scoped MatrixGroups

noncomputable section

abbrev RightCoset (H : Subgroup SL(2, ℤ)) :=
  Quotient (QuotientGroup.rightRel H)

def rightCosetMk (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : RightCoset H :=
  Quotient.mk _ g

@[instance_reducible] def rightCosetFintype
    (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] : Fintype (RightCoset H) :=
  letI := H.fintypeQuotientOfFiniteIndex
  Fintype.ofEquiv (SL(2, ℤ) ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm

def rightCosetMul (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    RightCoset H ≃ RightCoset H where
  toFun := Quotient.map' (fun a => a * g) (fun a b h => by
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      QuotientGroup.rightRel_apply.mp h)
  invFun := Quotient.map' (fun a => a * g⁻¹) (fun a b h => by
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      QuotientGroup.rightRel_apply.mp h)
  left_inv := fun q => Quotient.inductionOn q (fun a => by
    change rightCosetMk H (a * g * g⁻¹) = rightCosetMk H a
    rw [mul_assoc, mul_inv_cancel, mul_one])
  right_inv := fun q => Quotient.inductionOn q (fun a => by
    change rightCosetMk H (a * g⁻¹ * g) = rightCosetMk H a
    rw [mul_assoc, inv_mul_cancel, mul_one])

def cosetValue (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z) :
    RightCoset H → ℍ → ℂ :=
  Quotient.lift (fun g z => f (g • z)) (fun a b hab => by
    funext z
    have h : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    calc
      f (a • z) = f ((b * a⁻¹) • (a • z)) := (hf (b * a⁻¹) h (a • z)).symm
      _ = f (b • z) := by rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one])

theorem cosetValue_mk (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z)
    (g : SL(2, ℤ)) (z : ℍ) :
    cosetValue H f hf (rightCosetMk H g) z = f (g • z) :=
  rfl

theorem cosetValue_smul (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z)
    (q : RightCoset H) (g : SL(2, ℤ)) (z : ℍ) :
    cosetValue H f hf q (g • z) = cosetValue H f hf (rightCosetMul H g q) z := by
  refine Quotient.inductionOn q (fun a => ?_)
  change f (a • (g • z)) = f ((a * g) • z)
  rw [mul_smul]

def cosetProduct (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z)
    (c : ℂ) (z : ℍ) : ℂ :=
  letI := rightCosetFintype H
  ∏ q : RightCoset H, (cosetValue H f hf q z - c)

theorem cosetProduct_smul (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z)
    (c : ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    cosetProduct H f hf c (g • z) = cosetProduct H f hf c z := by
  letI := rightCosetFintype H
  unfold cosetProduct
  refine Fintype.prod_equiv (rightCosetMul H g) _ _ (fun q => ?_)
  rw [cosetValue_smul]

theorem finite_image_of_constant_coset_products (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (f : ℍ → ℂ) (hf : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, f (h • z) = f z)
    (hConst : ∀ c : ℂ, ∀ z w : ℍ, cosetProduct H f hf c z = cosetProduct H f hf c w) :
    (Set.range f).Finite := by
  letI := rightCosetFintype H
  let base : ℍ := ⟨Complex.I, by simp⟩
  refine (Set.finite_range (fun q : RightCoset H => cosetValue H f hf q base)).subset ?_
  rintro y ⟨z, rfl⟩
  have hAt : cosetProduct H f hf (f z) z = 0 := by
    unfold cosetProduct
    refine Finset.prod_eq_zero (Finset.mem_univ (rightCosetMk H 1)) ?_
    rw [cosetValue_mk, one_smul, sub_self]
  have hBase : cosetProduct H f hf (f z) base = 0 :=
    (hConst (f z) base z).trans hAt
  unfold cosetProduct at hBase
  obtain ⟨q, _, hq⟩ := Finset.prod_eq_zero_iff.mp hBase
  exact ⟨q, sub_eq_zero.mp hq⟩

end
end ManuscriptAudit.FiniteIndexWeightZeroCosets

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteIndexWeightZeroCosets.cosetValue_smul,
      ``ManuscriptAudit.FiniteIndexWeightZeroCosets.cosetProduct_smul,
      ``ManuscriptAudit.FiniteIndexWeightZeroCosets.finite_image_of_constant_coset_products] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
