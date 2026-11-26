import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree zero and epimorphisms of geometric étale skyscrapers

Degree-zero cohomology is the coefficient group because a point has a
unique element over the terminal étale object. The geometric
skyscraper carries an epimorphism to an epimorphism because the actual
presheaf maps are products of the given surjection.
-/

namespace ManuscriptAudit.GeometricSkyscraperCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The full small étale site has native small Ext groups. -/
theorem etaleSiteHasExt (S : Scheme.{u}) :
    HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) := by
  let D := Sheaf S.smallEtaleTopology AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u} D :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology S AddCommGrpCat.{u}
  letI : LocallySmall.{u} D := IsGrothendieckAbelian.locallySmall (C := D)
  letI : EnoughInjectives D := IsGrothendieckAbelian.enoughInjectives.{u} (C := D)
  exact hasExt_of_enoughInjectives D

attribute [local instance] etaleSiteHasExt

variable {S : Scheme.{u}} (Φ : S.smallEtaleTopology.Point.{u})

/-- Actual degree-zero étale cohomology of a geometric skyscraper. -/
def geometricSkyscraperHZeroEquiv (M : AddCommGrpCat.{u}) :
    Sheaf.H (Φ.skyscraperSheaf M) 0 ≃+ M := by
  let T := ⊤_ S.Etale
  letI : Unique (Φ.fiber.obj T) := Φ.uniqueFiberObj T terminalIsTerminal
  let e := (productUniqueIso (fun _ : Φ.fiber.obj T => M)).addCommGroupIsoToAddEquiv
  exact (Sheaf.H.equiv₀ (Φ.skyscraperSheaf M) (terminalIsTerminal (C := S.Etale))).trans e

private theorem epi_productMap {I : Type u} {M N : AddCommGrpCat.{u}} (f : M ⟶ N) [Epi f] :
    Epi (Pi.map fun _ : I => f) := by
  classical
  let A : I → AddCommGrpCat.{u} := fun _ => M
  let B : I → AddCommGrpCat.{u} := fun _ => N
  let g : (∏ᶜ A) ⟶ (∏ᶜ B) := Pi.map fun _ : I => f
  apply (AddCommGrpCat.epi_iff_surjective g).2
  intro b
  let y := Concrete.productEquiv B b
  choose x hx using fun i => (AddCommGrpCat.epi_iff_surjective f).1 inferInstance (y i)
  refine ⟨(Concrete.productEquiv A).symm x, ?_⟩
  apply (Concrete.productEquiv B).injective
  funext i
  change Pi.π B i (g ((Concrete.productEquiv A).symm x)) = y i
  rw [← ConcreteCategory.comp_apply, Pi.map_π, ConcreteCategory.comp_apply,
    Concrete.productEquiv_symm_apply_π]
  exact hx i

/-- In each étale neighborhood the skyscraper map of an epimorphism is epic. -/
theorem geometricSkyscraper_map_app_epi {M N : AddCommGrpCat.{u}} (f : M ⟶ N) [Epi f]
    (W : S.Etaleᵒᵖ) :
    Epi (((Φ.skyscraperSheafFunctor.map f).hom).app W) := by
  change Epi (Pi.map fun _ : Φ.fiber.obj W.unop => f)
  exact epi_productMap f

/-- Taking the geometric skyscraper preserves epimorphisms. -/
theorem geometricSkyscraper_preservesEpimorphisms :
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{u})).PreservesEpimorphisms where
  preserves {M N} f hf := by
    let F := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u}
    let g := Φ.skyscraperSheafFunctor.map f
    letI : Epi (F.map g) := (NatTrans.epi_iff_epi_app _).mpr (geometricSkyscraper_map_app_epi Φ f)
    constructor
    intro K x y hxy
    apply F.map_injective
    apply (cancel_epi (F.map g)).mp
    simpa only [← Functor.map_comp] using congrArg (fun a => F.map a) hxy

end

end ManuscriptAudit.GeometricSkyscraperCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GeometricSkyscraperCohomology.geometricSkyscraperHZeroEquiv,
      ``ManuscriptAudit.GeometricSkyscraperCohomology.geometricSkyscraper_map_app_epi,
      ``ManuscriptAudit.GeometricSkyscraperCohomology.geometricSkyscraper_preservesEpimorphisms] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
