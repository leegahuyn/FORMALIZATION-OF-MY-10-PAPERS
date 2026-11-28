import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.PicardGroup
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrimeLocalization

/-! The native Picard base-change homomorphism agrees with extension of
ideal classes under localization. It is an isomorphism at a principal prime. -/

namespace ManuscriptAudit.DedekindPicardLocalization

open CommRing TensorProduct
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private def integralIdealRepresentative (I : (Ideal R)⁰) :
    (ClassGroup.equivPic R (ClassGroup.mk0 I)) ≃ₗ[R] I.val := by
  let F := FractionRing R
  let V := FractionalIdeal.unitsMulEquivSubmodule (FractionalIdeal.mk0 F I)
  have h : ClassGroup.equivPic R (ClassGroup.mk0 I) = Submodule.unitsToPic R F V := by
    rw [ClassGroup.mk0_eq_quotientMk] <;> rfl
  rw [h]
  let e : I.val ≃ₗ[R] (V : Submodule R F) :=
    Submodule.equivMapOfInjective (Algebra.linearMap R F) (IsFractionRing.injective R F) I.val
  exact (Submodule.unitsToPicEquiv V).trans e.symm

variable (M : Submonoid R) (S : Type*) [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [IsLocalization M S]

/-- Tensor extension of the actual ideal module is the actual ideal map. -/
def idealTensorEquiv (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] (I.map (algebraMap R S)) := by
  rw [← Ideal.localized'_eq_map S M I]
  exact (IsLocalizedModule.isBaseChange M S
    (I.toLocalized' S M (Algebra.linearMap R S))).equiv

/-- The genuine Picard and class-group arrows commute with their canonical
comparison isomorphisms for a localization of Dedekind domains. -/
theorem equivPic_map (hM : M ≤ R⁰) (c : ClassGroup R) :
    letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr (IsLocalization.injective S hM)
    Pic.mapAlgebra R S (ClassGroup.equivPic R c) =
      ClassGroup.equivPic S (ClassGroup.extendedHom R S c) := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr (IsLocalization.injective S hM)
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  let J : (Ideal S)⁰ := ⟨I.val.map (algebraMap R S),
    mem_nonZeroDivisors_iff_ne_zero.mpr
      ((Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective S hM)).not.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp I.property))⟩
  have h : ClassGroup.extendedHom R S (ClassGroup.mk0 I) =
      ClassGroup.mk0 J := ClassGroup.extendedHom_mk0 R S I
  rw [h]
  apply Pic.ext_iff.mpr
  let P := ClassGroup.equivPic R (ClassGroup.mk0 I)
  let Q := ClassGroup.equivPic S (ClassGroup.mk0 J)
  change Nonempty (Pic.mk S (S ⊗[R] P) ≃ₗ[S] Q)
  exact ⟨(Pic.mk.linearEquiv S (S ⊗[R] P)).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl S S) (integralIdealRepresentative I)).trans
      ((idealTensorEquiv M S I.val).trans (integralIdealRepresentative J).symm))⟩

/-- Extension of actual invertible modules to the principal open of a
prime element in a Dedekind domain is a Picard-group isomorphism. -/
theorem mapAlgebra_bijective (p : R) (hp : Prime p) :
    Function.Bijective (Pic.mapAlgebra R (Localization.Away p)) := by
  let S := Localization.Away p
  letI : Fact (Prime p) := ⟨hp⟩
  letI : IsDomain S := Localization.Away.isDomain hp.ne_zero
  have hM : Submonoid.powers p ≤ R⁰ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero
  letI : IsDedekindDomain S := IsLocalization.isDedekindDomain R hM S
  let E := ((ClassGroup.equivPic R).symm.trans (DedekindPrimeLocalization.classEquiv p)).trans
    (ClassGroup.equivPic S)
  have h : (Pic.mapAlgebra R S : Pic R → Pic S) = E := by
    funext x
    have hx := equivPic_map (Submonoid.powers p) S hM ((ClassGroup.equivPic R).symm x)
    simpa only [E, MulEquiv.trans_apply, DedekindPrimeLocalization.classEquiv,
      MulEquiv.ofBijective_apply, DedekindPrimeLocalization.classMap,
      MulEquiv.apply_symm_apply] using hx
  rw [h]
  exact E.bijective

end

end ManuscriptAudit.DedekindPicardLocalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindPicardLocalization.idealTensorEquiv,
      ``ManuscriptAudit.DedekindPicardLocalization.equivPic_map,
      ``ManuscriptAudit.DedekindPicardLocalization.mapAlgebra_bijective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
