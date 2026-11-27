import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCohomologyMap
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitSheaf

/-! The comparison of the actual étale and pro-étale unit sheaves. -/

namespace ManuscriptAudit.EtaleProetaleUnitComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Preadditive
open EtaleProetaleInverseImage

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

local instance etaleHasExt : HasExt.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology AddCommGrpCat.{1}
  exact IsGrothendieckAbelian.hasExt _

abbrev etaleUnits :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{1}).obj
    (KummerUnitsSheaf.fullCoordinateUnitSheaf X)

abbrev proetaleUnits := ProetaleUnitSheaf.unitSheaf X

/-- Restriction of the actual pro-étale unit sheaf is the actual small étale unit sheaf. -/
def directImageUnitsIso : (directImage X).obj (proetaleUnits X) ≅ etaleUnits X := by
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{1}
  have h : G.obj ((directImage X).obj (proetaleUnits X)) ≅ G.obj (etaleUnits X) :=
    Iso.refl _
  exact G.preimageIso h

/-- The canonical comparison sends pulled-back étale units to actual pro-étale units. -/
def unitComparison : (inverseImage X).obj (etaleUnits X) ⟶ proetaleUnits X :=
  ((adjunction X).homEquiv (etaleUnits X) (proetaleUnits X)).symm (directImageUnitsIso X).inv

theorem unitComparison_power_naturality (d : ℕ) :
    (inverseImage X).map (d • 𝟙 (etaleUnits X)) ≫ unitComparison X =
      unitComparison X ≫ (d • 𝟙 (proetaleUnits X)) := by
  letI : (inverseImage X).Additive := Functor.additive_of_preserves_binary_products (inverseImage X)
  rw [Functor.map_nsmul, Functor.map_id, nsmul_comp, id_comp, comp_nsmul, comp_id]

/-- The unit coefficient comparison gives actual derived maps in every degree. -/
def unitCohomologyComparison (n : ℕ) :
    Sheaf.H (etaleUnits X) n →+ Sheaf.H (proetaleUnits X) n :=
  (Sheaf.H.map (unitComparison X) n).comp
    (EtaleProetaleCohomologyMap.pullback X (etaleUnits X) n)

end
end ManuscriptAudit.EtaleProetaleUnitComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleUnitComparison.directImageUnitsIso,
      ``ManuscriptAudit.EtaleProetaleUnitComparison.unitComparison_power_naturality,
      ``ManuscriptAudit.EtaleProetaleUnitComparison.unitCohomologyComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
