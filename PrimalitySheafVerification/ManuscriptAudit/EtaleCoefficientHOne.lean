import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientUniverseLift
import PrimalitySheafVerification.ManuscriptAudit.ExtOneFullyFaithful
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-! Actual degree-one small étale cohomology embeds under the coefficient universe lift. -/

namespace ManuscriptAudit.EtaleCoefficientHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open EtaleCoefficientUniverseLift (lift constantIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}

private abbrev C := Sheaf X.smallEtaleTopology A
private abbrev D := Sheaf X.smallEtaleTopology B

private theorem lowGrothendieck : IsGrothendieckAbelian.{0} (C X) :=
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X A

private theorem highGrothendieck : IsGrothendieckAbelian.{1} (D X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology B

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] lowGrothendieck highGrothendieck

local instance highExt : HasExt.{1} (D X) := IsGrothendieckAbelian.hasExt (D X)

local instance lowInjectives : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{0} (C := C X)

private abbrev Z₀ := (constantSheaf X.smallEtaleTopology A).obj (AddCommGrpCat.of (ULift.{0} ℤ))
private abbrev Z₁ := (constantSheaf X.smallEtaleTopology B).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private def zEquiv : ULift.{1} (ULift.{0} ℤ) ≃+ ULift.{1} ℤ where
  toFun x := ⟨x.down.down⟩
  invFun x := ⟨⟨x.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def integerIso : (lift X).obj (Z₀ X) ≅ Z₁ X :=
  (constantIso X).app (AddCommGrpCat.of (ULift.{0} ℤ)) ≪≫
    (constantSheaf X.smallEtaleTopology B).mapIso zEquiv.toAddCommGrpIso

/-- The actual additive comparison of H¹ across coefficient universes. -/
def comparison (F : C X) : Sheaf.H F 1 →+ Sheaf.H ((lift X).obj F) 1 :=
  ((Ext.mk₀ (integerIso X).inv).precomp ((lift X).obj F) (zero_add 1)).comp
    ((lift X).mapExtAddHom (Z₀ X) F 1)

/-- The native H¹ comparison for the coefficient lift is injective. -/
theorem comparison_injective (F : C X) : Function.Injective (comparison X F) := by
  have h : Function.LeftInverse
      ((Ext.mk₀ (integerIso X).hom).precomp ((lift X).obj F) (zero_add 1))
      ((Ext.mk₀ (integerIso X).inv).precomp ((lift X).obj F) (zero_add 1)) := by
    intro e
    change (Ext.mk₀ (integerIso X).hom).comp
      ((Ext.mk₀ (integerIso X).inv).comp e (zero_add 1)) (zero_add 1) = e
    rw [Ext.mk₀_comp_mk₀_assoc, (integerIso X).hom_inv_id, Ext.mk₀_id_comp]
  intro a b hab
  apply ExtOneFullyFaithful.map_injective (lift X) (Z₀ X) F
  apply h.injective
  exact hab

end
end ManuscriptAudit.EtaleCoefficientHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleCoefficientHOne.comparison_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
