import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import PrimalitySheafVerification.ManuscriptAudit.SkyscraperHOne

/-!
# First cohomology of finite sums of skyscrapers

Products of flasque abelian sheaves are flasque, since their sections and
restriction maps are computed coordinatewise. A finite coproduct is a
product, so all of Paper 6's finite-stage sums have zero first cohomology.
-/

namespace ManuscriptAudit.FiniteSkyscraperSumHOne

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.SkyscraperHOne

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private def evalType {X : TopCat.{0}} (U : (Opens X)ᵒᵖ) : AbelianSheaf X ⥤ Type :=
  (sheafToPresheaf (Opens.grothendieckTopology X) G ⋙ (evaluation _ G).obj U) ⋙
    CategoryTheory.forget G

private instance {X : TopCat.{0}} (U : (Opens X)ᵒᵖ) : PreservesLimits (evalType U) := by
  unfold evalType
  infer_instance

private def sectionsProdIso {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X)
    (U : (Opens X)ᵒᵖ) :
    ((∏ᶜ S).obj.obj U : Type) ≅ (∀ i, ((S i).obj.obj U : Type)) :=
  PreservesProduct.iso (evalType U) S ≪≫ Types.productIso.{0, 0} _

private theorem sectionsProdIso_apply {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X)
    (U : (Opens X)ᵒᵖ) (z : (∏ᶜ S).obj.obj U) (i : ι) :
    (sectionsProdIso S U).toEquiv z i = (Pi.π S i).hom.app U z := by
  change (((PreservesProduct.iso (evalType U) S).hom ≫ (Types.productIso.{0, 0} _).hom) ≫
    (↾fun f => f i)) z = _
  rw [Category.assoc, Types.productIso_hom_comp_eval, PreservesProduct.iso_hom,
    piComparison_comp_π]
  rfl

/-- A product of flasque abelian sheaves is flasque. -/
theorem product_isFlasque {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X)
    (hS : ∀ i, TopCat.Sheaf.IsFlasque (S i)) :
    TopCat.Sheaf.IsFlasque (∏ᶜ S) := by
  classical
  constructor
  intro U V r
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro z
  let eU := (sectionsProdIso S U).toEquiv
  let eV := (sectionsProdIso S V).toEquiv
  have hLift (i : ι) : ∃ t : (S i).obj.obj U, (S i).obj.map r t = eV z i := by
    letI := hS i
    exact (AddCommGrpCat.epi_iff_surjective _).1 inferInstance (eV z i)
  choose f hf using hLift
  let t := eU.symm f
  refine ⟨t, eV.injective ?_⟩
  funext i
  have hn := DFunLike.congr_fun ((Pi.π S i).hom.naturality r) t
  calc
    eV ((∏ᶜ S).obj.map r t) i =
        (Pi.π S i).hom.app V ((∏ᶜ S).obj.map r t) :=
      sectionsProdIso_apply S V _ i
    _ = (S i).obj.map r ((Pi.π S i).hom.app U t) := hn
    _ = (S i).obj.map r (f i) := by
      rw [← sectionsProdIso_apply]
      exact congrArg ((S i).obj.map r) (congrFun (eU.apply_symm_apply f) i)
    _ = eV z i := hf i

/-- Every finite coproduct of flasque abelian sheaves has zero native H¹. -/
theorem finiteCoproduct_H1_subsingleton {X : TopCat.{0}} {ι : Type} [Finite ι]
    (S : ι → AbelianSheaf X) (hS : ∀ i, TopCat.Sheaf.IsFlasque (S i)) :
    Subsingleton ((∐ S).H 1) := by
  letI := product_isFlasque S hS
  letI := flasque_H1_subsingleton (∏ᶜ S)
  let e := biproductIso S
  let eH := (Sheaf.functorH (Opens.grothendieckTopology X) 1).mapIso e
  exact eH.symm.addCommGroupIsoToAddEquiv.injective.subsingleton

/-- The actual skyscraper sheaf with an arbitrary abelian coefficient. -/
def pointSummand {X : TopCat.{0}} (p : X) (A : G) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf p A

theorem pointSummand_isFlasque {X : TopCat.{0}} (p : X) (A : G) :
    TopCat.Sheaf.IsFlasque (pointSummand p A) := by
  classical
  exact TopCat.isFlasque_skyscraperSheaf_of_hasZeroObject p A

/-- The finite-stage skyscraper sums in Paper 6 have zero native H¹. -/
theorem finiteSkyscraperCoproduct_H1_subsingleton {X : TopCat.{0}} {ι : Type} [Finite ι]
    (p : ι → X) (A : ι → G) : Subsingleton ((∐ fun i => pointSummand (p i) (A i)).H 1) :=
  finiteCoproduct_H1_subsingleton _ (fun i => pointSummand_isFlasque (p i) (A i))

end

end ManuscriptAudit.FiniteSkyscraperSumHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteSkyscraperSumHOne.product_isFlasque,
      ``ManuscriptAudit.FiniteSkyscraperSumHOne.finiteCoproduct_H1_subsingleton,
      ``ManuscriptAudit.FiniteSkyscraperSumHOne.finiteSkyscraperCoproduct_H1_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
