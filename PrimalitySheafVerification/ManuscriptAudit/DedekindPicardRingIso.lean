import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindPicardLocalization
import PrimalitySheafVerification.ManuscriptAudit.DedekindClassMapIntegral

/-! The actual Picard pullback by a ring isomorphism is the actual
transport of fractional ideal classes. -/

namespace ManuscriptAudit.DedekindPicardRingIso

open CommRing
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
variable (e : A ≃+* B)

/-- Interpret the actual ring equivalence as an algebra by its literal ring map. -/
abbrev algebra : Algebra A B := e.toRingHom.toAlgebra

/-- A ring isomorphism is the localization at just the unit one. -/
theorem isLocalization :
    letI : Algebra A B := algebra e
    IsLocalization (⊥ : Submonoid A) B := by
  letI : Algebra A B := algebra e
  letI : IsLocalization (⊥ : Submonoid A) A :=
    IsLocalization.of_le_isUnit (show (⊥ : Submonoid A) ≤ IsUnit.submonoid A from bot_le)
  let ex : A ≃ₐ[A] B :=
    { e with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid A) ex

/-- The genuine Picard extension by a ring isomorphism commutes with
the native class-group isomorphism of the same ring map. -/
theorem equivPic_map (x : ClassGroup A) :
    letI : Algebra A B := algebra e
    Pic.mapAlgebra A B (ClassGroup.equivPic A x) =
      ClassGroup.equivPic B (ClassGroup.mulEquiv e x) := by
  letI : Algebra A B := algebra e
  letI : IsLocalization (⊥ : Submonoid A) B := isLocalization e
  letI : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr e.injective
  have h := DedekindPicardLocalization.equivPic_map (⊥ : Submonoid A) B
    (show (⊥ : Submonoid A) ≤ A⁰ from bot_le) x
  have he : ClassGroup.extendedHom A B x = ClassGroup.mulEquiv e x := by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
    rw [ClassGroup.extendedHom_mk0 A B I, DedekindClassMapIntegral.class_mk0_map]
    rfl
  exact h.trans (congrArg (ClassGroup.equivPic B) he)

end

end ManuscriptAudit.DedekindPicardRingIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindPicardRingIso.equivPic_map
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
