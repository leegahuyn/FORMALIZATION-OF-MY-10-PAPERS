import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-!
# Units admit cokernel lifts over field charts

On an actual étale object with underlying scheme the spectrum of a
field, the restriction of the unit sheaf has vanishing degree-one
cohomology. Exact restriction therefore gives surjective quotient
sections for any monomorphism out of the unit sheaf.
-/

namespace ManuscriptAudit.EtaleObjectRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

set_option maxHeartbeats 2600000 in
/-- Any quotient section of a monomorphism out of the units lifts
over an étale object whose underlying scheme is a field spectrum. -/
theorem unitsCokernel_sections_surjective_of_field
    {X : Scheme.{0}} {M : Sheaf X.smallEtaleTopology AddCommGrpCat.{0}}
    (i : fullCoordinateUnitSheaf X ⟶ M) [Mono i]
    (W : X.Etale) (L : Type) [Field L] (e : W.left ≅ Spec (CommRingCat.of L)) :
    Function.Surjective ((cokernel.π i).hom.app (op W)) := by
  let U := Spec (CommRingCat.of L)
  let j : U ⟶ X := e.inv ≫ W.hom
  letI : Etale W.hom := W.prop
  letI : Etale j := by change Etale (e.inv ≫ W.hom); infer_instance
  let R := restriction j
  letI : R.IsLeftAdjoint := (restrictionAdjunction j).isLeftAdjoint
  letI : PreservesFiniteLimits R := restriction_preservesFiniteLimits j
  letI : R.Additive := R.additive_of_preserves_binary_products
  let T : U.Etale := Scheme.Etale.mk (𝟙 U)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale U
  let S := ShortComplex.cokernelSequence i
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) (inferInstanceAs (Mono i))
    (inferInstanceAs (Epi (cokernel.π i)))
  let S' := S.map R
  have hS' : S'.ShortExact := hS.map_of_exact R
  let hIso := ((Sheaf.functorH U.smallEtaleTopology 1).mapIso
    (restrictionUnitsIso j)).addCommGroupIsoToAddEquiv
  have h := unitHOne_subsingleton_of_pid L
  have hv : Subsingleton (Sheaf.H S'.X₁ 1) :=
    ⟨fun a b ↦ hIso.injective (h.allEq (hIso a) (hIso b))⟩
  let V := (postcompose j).obj T
  let e' : V ≅ W := MorphismProperty.Over.isoMk e.symm (by
    change e.inv ≫ W.hom = 𝟙 U ≫ j
    exact (Category.id_comp j).symm)
  let Q := cokernel i
  let π : M ⟶ Q := cokernel.π i
  have hSurj : Function.Surjective (π.hom.app (op V)) :=
    SheafShortExactSections.sections_surjective_of_HOne S' hS' hT hv
  intro y
  obtain ⟨x, hx⟩ := hSurj (Q.obj.map e'.hom.op y)
  refine ⟨M.obj.map e'.inv.op x, ?_⟩
  calc
    _ = Q.obj.map e'.inv.op (π.hom.app (op V) x) :=
      ConcreteCategory.congr_hom (π.hom.naturality e'.inv.op) x
    _ = _ := by
      rw [hx]
      exact ((Q.obj.mapIso e'.op).addCommGroupIsoToAddEquiv).symm_apply_apply y

end

end ManuscriptAudit.EtaleObjectRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleObjectRestriction.unitsCokernel_sections_surjective_of_field
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
