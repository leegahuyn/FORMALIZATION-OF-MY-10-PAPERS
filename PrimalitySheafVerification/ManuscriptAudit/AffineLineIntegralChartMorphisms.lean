import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineIntegralChartCoordinates
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitNaturality

/-!
# Canonical algebra maps for morphisms of integral affine charts

A native affine étale arrow is induced by its opposite coordinate
ring homomorphism. The coordinate chart isomorphisms identify the
original arrow with the chart arrow of this algebra map.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable {U V : (X K).AffineEtale}

/-- A native affine étale arrow induces a homomorphism of coordinate algebras. -/
def coordinateMap (g : V ⟶ U) :
    letI := coordinateAlgebra K U
    letI := coordinateAlgebra K V
    coordinateRing K U →ₐ[Polynomial K] coordinateRing K V := by
  letI := coordinateAlgebra K U
  letI := coordinateAlgebra K V
  refine { g.left.unop.hom with commutes' := fun r ↦ ?_ }
  have h : Spec.map g.left.unop ≫ U.hom = V.hom := by
    have hw := g.w
    change Spec.map g.left.unop ≫ U.hom = V.hom ≫ 𝟙 (X K) at hw
    exact hw.trans (Category.comp_id V.hom)
  have h' : Spec.preimage U.hom ≫ g.left.unop = Spec.preimage V.hom := by
    simpa only [Spec.preimage_comp, Spec.preimage_map] using congrArg Spec.preimage h
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') r

/-- The actual coordinate chart isomorphisms identify each native arrow
with the affine étale arrow of its coordinate map. -/
theorem coordinateMap_chart_comm (g : V ⟶ U)
    (hU : IsDomain (coordinateRing K U)) (hV : IsDomain (coordinateRing K V)) :
    letI := coordinateAlgebra K U
    letI := coordinateAlgebra K V
    letI := coordinateAlgebra_etale K U
    letI := coordinateAlgebra_etale K V
    letI := hU
    letI := hV
    (coordinateChartIso K V hV).hom ≫ g =
      (Scheme.AffineEtale.Spec (X K)).preimage
        (X := chartObject K (coordinateRing K V)) (Y := chartObject K (coordinateRing K U))
        (algebraEtaleMap (coordinateMap K g)) ≫
        (coordinateChartIso K U hU).hom := by
  letI := coordinateAlgebra K U
  letI := coordinateAlgebra K V
  letI := coordinateAlgebra_etale K U
  letI := coordinateAlgebra_etale K V
  letI := hU
  letI := hV
  let G := Scheme.AffineEtale.Spec (X K)
  apply G.map_injective
  rw [Functor.map_comp, Functor.map_comp, G.map_preimage]
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (𝟙 (coordinateRing K V)) ≫ Spec.map g.left.unop =
    Spec.map (CommRingCat.ofHom (coordinateMap K g).toRingHom) ≫
      Spec.map (𝟙 (coordinateRing K U))
  rw [Spec.map_id, Spec.map_id, Category.id_comp]
  exact (congrArg Spec.map (CommRingCat.ofHom_hom g.left.unop).symm).trans
    (Category.comp_id _).symm

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.coordinateMap_chart_comm
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
