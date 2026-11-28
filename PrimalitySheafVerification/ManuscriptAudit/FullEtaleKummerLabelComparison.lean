import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRootLabelCompatibility
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSheafificationUnit
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleConstantRootLabel
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerConstantTransition

/-! The direct full-site Kummer label is the identical map that
underlies the existing finite-level Kummer isomorphisms. -/

namespace ManuscriptAudit.FullEtaleKummerLabelComparison

open AlgebraicGeometry CategoryTheory Opposite
open FullEtaleKummerConstantTransition FullEtaleConstantRootLabel
open KummerUnitsSheaf KummerUnitsPresheaf KummerSheafSequence
open KummerConstantCoefficients (coefficientGroup)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev G (X : Scheme.{0}) := fullCoordinateUnitSheaf X
private abbrev J (X : Scheme.{0}) := Scheme.AffineEtale.topology X
private abbrev L (X : Scheme.{0}) := presheafToSheaf (J X) A
private abbrev a (X : Scheme.{0}) := sheafificationAdjunction (J X) A
private abbrev C (X : Scheme.{0}) := constantSheaf X.smallEtaleTopology A
private abbrev E (X : Scheme.{0}) := Scheme.AffineEtale.sheafEquiv X A
private abbrev S := KummerRelativeFull.sequence
private abbrev W (X : Scheme.{0}) :=
  (Functor.whiskeringLeft X.AffineEtaleᵒᵖ X.Etaleᵒᵖ A).obj (Scheme.AffineEtale.Spec X).op

variable {X : Scheme.{0}} {K : Type} [Field K]
variable (k : X ⟶ Spec (CommRingCat.of K))

private abbrev F (d : ℕ) := (Functor.const X.Etaleᵒᵖ).obj (coefficientGroup K d)
private abbrev c (d : ℕ) := (AffineEtaleSheafificationUnit.comparison X).app (F (X := X) (K := K) d)

private def v : (E X).inverse.obj (G X) ≅ unitSheaf X :=
  (fullyFaithfulSheafToPresheaf (J X) A).preimageIso (affineRestrictionUnitsIso X) ≪≫
    coordinateUnitSheafIso X

private theorem unitsIso_hom (d : ℕ) :
    (KummerRelativeFull.unitsIso (X := X) d).hom =
      (E X).counitIso.inv.app (G X) ≫ (E X).functor.map (v (X := X)).hom := rfl

private theorem affine_label (d : ℕ) :
    (E X).inverse.map (unitLabel k d) ≫ (v (X := X)).hom =
      (c (X := X) (K := K) d).inv ≫ (L X).map (EtaleKummerCyclicCoordinates.label k d) := by
  let e := c (X := X) (K := K) d
  let P := (W X).obj (F (X := X) (K := K) d)
  let f := EtaleKummerCyclicCoordinates.label k d
  let g := FullEtaleRootLabelsSemilinear.label k d
  let u := (v (X := X)).hom
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply ((a X).homEquiv P (unitSheaf X)).injective
  have he : (a X).homEquiv P ((E X).inverse.obj (G X))
      (e.hom ≫ (E X).inverse.map (unitLabel k d)) = (W X).map g :=
    AffineEtaleSheafificationUnit.comparison_postcompose X _ (G X) g
  calc
    _ = (W X).map g ≫ u.hom := by
      rw [← Category.assoc, (a X).homEquiv_naturality_right, he]
    _ = f ≫ (a X).unit.app (units X) := by
      change (W X).map g ≫ (affineRestrictionUnitsIso X).hom ≫ (a X).unit.app (units X) = _
      rw [← Category.assoc, AffineEtaleRootLabelCompatibility.label_affine k d]
    _ = _ := by
      rw [Adjunction.homEquiv_unit]
      exact ((a X).unit.naturality f)

variable [IsAlgClosed K] (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

/-- The literal full-site label into units is precisely the inclusion
in the Kummer comparison used for the compatible Tate tower. -/
theorem unitLabel_eq_kummer (n : ℕ) :
    unitLabel k (l ^ n) ≫ (KummerRelativeFull.unitsIso (X := X) (l ^ n)).hom =
      (constantKernelIso k l n).hom ≫ (S X (l ^ n)).f := by
  let d := l ^ n
  let f := unitLabel k d
  let u := (v (X := X)).hom
  have hc := (E X).counitIso.inv.naturality f
  change f ≫ (E X).counitIso.inv.app (G X) =
    (E X).counitIso.inv.app ((C X).obj (coefficientGroup K d)) ≫
      (E X).functor.map ((E X).inverse.map f) at hc
  rw [unitsIso_hom, ← Category.assoc, hc, Category.assoc, ← Functor.map_comp, affine_label]
  exact (constantKernel_toUnits k l n).symm

end

end ManuscriptAudit.FullEtaleKummerLabelComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleKummerLabelComparison.unitLabel_eq_kummer
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
