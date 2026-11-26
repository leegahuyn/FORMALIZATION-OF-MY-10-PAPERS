import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.CategoryTheory.Sites.Point.Comap
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleGeometricBaseChange

/-!
# Geometric skyscrapers and small étale direct image

The direct image of a geometric skyscraper along a scheme morphism
is the skyscraper at the image geometric point. In particular this is
the actual direct image from the rational cusp origin.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SmallEtaleBaseChange

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Z X : Scheme.{u}} (i : Z ⟶ X)
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- Direct image on the actual small étale sites carries a geometric
skyscraper to the skyscraper at the composite geometric point. -/
def geometricSkyscraperDirectImageIso :
    (Scheme.pointSmallEtale s).skyscraperSheafFunctor ⋙ directImage i C.{u} ≅
      (Scheme.pointSmallEtale (s ≫ i)).skyscraperSheafFunctor := by
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Scheme.pointSmallEtale (s ≫ i)
  let G := etaleBaseChange i
  let e := geometricFiberBaseChangeIso i s
  letI := SmallEtaleBaseChange.preservesFiniteLimits i
  letI := flat_of_preservesFiniteLimits G
  letI := isContinuous_of_baseChange i
  let eElements : (G ⋙ Φ.fiber).Elements ≌ Ψ.fiber.Elements :=
    Cat.equivOfIso (Functor.elementsFunctor.mapIso e)
  letI : InitiallySmall.{u} Ψ.fiber.Elements := Ψ.initiallySmall
  letI : InitiallySmall.{u} (G ⋙ Φ.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall eElements.inverse
  let cov := SmallEtaleBaseChange.coverPreserving i
  let T := Φ.comap G cov
  let f : T ⟶ Ψ := ⟨e.inv⟩
  let g : Ψ ⟶ T := ⟨e.hom⟩
  have hfg : f ≫ g = 𝟙 T := GrothendieckTopology.Point.hom_ext e.hom_inv_id
  have hgf : g ≫ f = 𝟙 Ψ := GrothendieckTopology.Point.hom_ext e.inv_hom_id
  let eFib : T.sheafFiber (A := C.{u}) ≅ Ψ.sheafFiber :=
    { hom := g.sheafFiber
      inv := f.sheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, hfg,
          GrothendieckTopology.Point.Hom.sheafFiber_id]
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, hgf,
          GrothendieckTopology.Point.Hom.sheafFiber_id] }
  exact Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous G cov C.{u} ≪≫
    (T.skyscraperSheafAdjunction.ofNatIsoLeft eFib).rightAdjointUniq Ψ.skyscraperSheafAdjunction

/-- Direct image from the exact rational cusp origin sends the geometric
skyscraper on the residue field to the geometric origin skyscraper. -/
def cuspOriginSkyscraperDirectImageIso (K : Type u) [Field K] [IsSepClosed K] :
    (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of K)))).skyscraperSheafFunctor ⋙
        directImage (cuspOrigin K) C.{u} ≅
      (Scheme.pointSmallEtale (cuspOrigin K)).skyscraperSheafFunctor :=
  geometricSkyscraperDirectImageIso (cuspOrigin K) (𝟙 _) ≪≫
    eqToIso (by rw [Category.id_comp])

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleGeometricBaseChange.geometricSkyscraperDirectImageIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOriginSkyscraperDirectImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
