import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericUnitComparison
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitQuotient

/-! The genuine generic-unit quotient restricts to the native quotient
on an affine open through which the point factors. -/

namespace ManuscriptAudit.OpenEtaleGenericUnitQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenEtaleExtension OpenEtaleGenericUnitComparison GenericEtaleUnitSections

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (g : Y ⟶ U)

private abbrev R := restriction j AddCommGrpCat.{0}

local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1
local instance : PreservesFiniteColimits (R j) := (restriction_exact j).2
local instance : (R j).Additive := restriction_additive j

/-- Exact restriction identifies the actual quotient with the native one
for the factored morphism into the open. -/
def quotientIso :
    (R j).obj (cokernel (pullbackToDirectImage (g ≫ j))) ≅ cokernel (pullbackToDirectImage g) :=
  PreservesCokernel.iso (R j) _ ≪≫ cokernel.mapIso _ _
    (EtaleObjectRestriction.restrictionUnitsIso j) (genericUnitsIso j g) (genericUnitsSquare j g)

/-- This quotient comparison respects the genuine quotient arrow. -/
theorem quotientIso_projection :
    (R j).map (cokernel.π (pullbackToDirectImage (g ≫ j))) ≫ (quotientIso j g).hom =
    (genericUnitsIso j g).hom ≫ cokernel.π (pullbackToDirectImage g) := by
  unfold quotientIso
  rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
  simp [cokernel.mapIso]

/-- Regular-to-generic units remain monic upon restriction to the
factoring open whenever its native units map is monic. -/
theorem mono_restriction [Mono (pullbackToDirectImage g)] :
    Mono ((R j).map (pullbackToDirectImage (g ≫ j))) := by
  refine ⟨fun {T} a b h => ?_⟩
  apply (cancel_mono ((EtaleObjectRestriction.restrictionUnitsIso j).hom ≫
    pullbackToDirectImage g)).mp
  rw [← genericUnitsSquare j g, ← Category.assoc, ← Category.assoc, h]

end

end ManuscriptAudit.OpenEtaleGenericUnitQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleGenericUnitQuotient.quotientIso_projection,
      ``ManuscriptAudit.OpenEtaleGenericUnitQuotient.mono_restriction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
