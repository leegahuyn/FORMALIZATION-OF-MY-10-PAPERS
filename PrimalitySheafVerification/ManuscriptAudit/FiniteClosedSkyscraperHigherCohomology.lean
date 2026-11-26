import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Biproducts
import PrimalitySheafVerification.ManuscriptAudit.FiniteClosedSkyscraperDecomposition
import PrimalitySheafVerification.ManuscriptAudit.ZariskiSkyscraperHigherCohomology

/-!
# Finite closed support and higher Zariski cohomology

The canonical finite skyscraper decomposition and additivity of the
cohomology functors give vanishing in every positive degree and identify
degree zero with the product of the actual stalk groups.
-/

namespace ManuscriptAudit.FiniteClosedSkyscraperHigherCohomology

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ClosedPointSupportDetection
open ManuscriptAudit.FiniteClosedSkyscraperDecomposition
open ManuscriptAudit.FiniteSkyscraperSumHOne ManuscriptAudit.ZariskiSkyscraperHigherCohomology
open TopologicalSpace

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev AGrp := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

local instance sheaf_hasCoproduct {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X) :
    HasCoproduct S := abelianSheaf_hasDiscreteColimit X (Discrete.functor S)

/-- Degree-zero Zariski cohomology is the product of the stalk groups. -/
def H0_addEquiv_stalkProduct {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) [Finite P]
    (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X)) (hSupport : stalkSupport F ⊆ P) :
    F.H 0 ≃+ ((p : P) → TopCat.Presheaf.stalk (C := AGrp) F.obj (p : X)) := by
  classical
  let S : P → AbelianSheaf X := FiniteClosedSkyscraperDecomposition.pointFactor F P
  let B : P → AGrp := fun p => TopCat.Presheaf.stalk (C := AGrp) F.obj (p : X)
  let H := Sheaf.functorH (Opens.grothendieckTopology X) 0
  letI : PreservesBiproduct S H := inferInstance
  letI : PreservesLimit (Discrete.functor S) H := preservesProduct_of_preservesBiproduct H
  let hT : IsTerminal (⊤ : Opens X) :=
    IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)
  let e (p : P) : H.obj (S p) ≅ B p := by
    have hp : (S p).obj.obj (op (⊤ : Opens X)) = B p := by
      change (if (p : X) ∈ (⊤ : Opens X) then B p else terminal AGrp) = B p
      rw [if_pos (Opens.mem_top _)]
    exact (Sheaf.H.equiv₀ (S p) hT).toAddCommGrpIso ≪≫ eqToIso hp
  letI : HasBiproduct B := HasBiproduct.of_hasProduct B
  let eProduct : (∏ᶜ B) ≅ AddCommGrpCat.of (∀ p : P, B p) :=
    (biproduct.isoProduct B).symm ≪≫ AddCommGrpCat.biproductIsoPi B
  exact (H.mapIso (pointProductIso F P hClosed hSupport) ≪≫
    PreservesProduct.iso H S ≪≫ Pi.mapIso e ≪≫ eProduct).addCommGroupIsoToAddEquiv

/-- Every positive degree of native Zariski sheaf cohomology vanishes for a sheaf
with stalk support contained in a finite set of closed points. -/
theorem H_succ_subsingleton_of_finite_closed_support {X : TopCat.{0}} (F : AbelianSheaf X)
    (P : Set X) [Finite P] (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X))
    (hSupport : stalkSupport F ⊆ P) (n : ℕ) : Subsingleton (F.H (n + 1)) := by
  let S : P → AbelianSheaf X := FiniteClosedSkyscraperDecomposition.pointFactor F P
  letI : HasBiproduct S := HasBiproduct.of_hasProduct S
  let e : F ≅ ∐ S := pointProductIso F P hClosed hSupport ≪≫ biproductIso S
  let H := Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)
  letI : PreservesBiproduct S H := inferInstance
  letI : PreservesColimit (Discrete.functor S) H := preservesCoproduct_of_preservesBiproduct H
  have hZero (p : P) : IsZero (H.obj (S p)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      (pointSummand_H_succ_subsingleton (p : X)
        (TopCat.Presheaf.stalk (C := AGrp) F.obj (p : X)) n)
  letI : Subsingleton (H.obj (∐ S)) :=
    AddCommGrpCat.subsingleton_of_isZero (mapCoproduct_isZero H S hZero)
  exact (H.mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton

end

end ManuscriptAudit.FiniteClosedSkyscraperHigherCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteClosedSkyscraperHigherCohomology.H0_addEquiv_stalkProduct,
      ``ManuscriptAudit.FiniteClosedSkyscraperHigherCohomology.H_succ_subsingleton_of_finite_closed_support] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
