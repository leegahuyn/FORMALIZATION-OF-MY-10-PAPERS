import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Ordinary native restriction to an actual open is natural for maps of
continuous coefficients, including the genuine finite residue maps. -/

namespace ManuscriptAudit.ProetaleOpenRestrictionCoefficientNaturality

open AlgebraicGeometry CategoryTheory Opposite
open OpenProetaleExtension (restriction)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleContinuousCoefficientNaturality (map)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{1}
private abbrev R := restriction j A

private theorem restrictionFunctionsIso_app (T : Type) [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] (V : U.ProEtᵒᵖ) :
    (restrictionFunctionsIso j T).hom.hom.app V = 𝟙 ((functions T U).obj.obj V) := by
  let G := sheafToPresheaf (Scheme.ProEt.topology U) A
  change (G.map (restrictionFunctionsIso j T).hom).app V = _
  rw [restrictionFunctionsIso, Functor.preimageIso_hom]
  change (G.map (G.preimage _)).app V = _
  rw [G.map_preimage] <;> rfl

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
variable (f : M →+ N) (hf : Continuous f)

theorem restrictionFunctionsIso_naturality :
    (R j).map (map f hf X) ≫ (restrictionFunctionsIso j N).hom =
      (restrictionFunctionsIso j M).hom ≫ map f hf U := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change ((R j).map (map f hf X)).hom.app V ≫ (restrictionFunctionsIso j N).hom.hom.app V =
    (restrictionFunctionsIso j M).hom.hom.app V ≫ (map f hf U).hom.app V
  simp only [restrictionFunctionsIso_app, Category.comp_id, Category.id_comp] <;> rfl

/-- The native ordinary cohomology on an open commutes with actual continuous coefficient maps. -/
theorem restrictionH_naturality (d : ℕ) (x : Sheaf.H ((R j).obj (functions M X)) d) :
    cohomologyIso (X := U) (restrictionFunctionsIso j N) d
        (Sheaf.H.map ((R j).map (map f hf X)) d x) =
      Sheaf.H.map (map f hf U) d
        (cohomologyIso (X := U) (restrictionFunctionsIso j M) d x) := by
  let g := (R j).map (map f hf X)
  let i := (restrictionFunctionsIso j N).hom
  let e := (restrictionFunctionsIso j M).hom
  let h := map f hf U
  calc
    _ = Sheaf.H.map (g ≫ i) d x := (Sheaf.H.map_comp_apply g i x).symm
    _ = Sheaf.H.map (e ≫ h) d x := congrArg (fun t ↦ Sheaf.H.map t d x)
      (restrictionFunctionsIso_naturality j f hf)
    _ = _ := Sheaf.H.map_comp_apply e h x

end
end ManuscriptAudit.ProetaleOpenRestrictionCoefficientNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenRestrictionCoefficientNaturality.restrictionH_naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
