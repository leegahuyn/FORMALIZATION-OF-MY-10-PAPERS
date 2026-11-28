import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap

/-! Ambient small étale restriction compared with the literal affine
basis on smaller opens. -/

namespace ManuscriptAudit.NestedAffineEtaleRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension AffineEtaleOpenRestriction OpenEtaleHOneByRepresentatives
open AffineEtaleTensorOverlap

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
private abbrev C := AddCommGrpCat.{u}
private abbrev E (Y : Scheme.{u}) := Scheme.AffineEtale.sheafEquiv Y C.{u}

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]

/-- Restrict an ambient small étale sheaf to the affine basis of an actual open. -/
def restrictToAffine :
    Sheaf X.smallEtaleTopology C.{u} ⥤ Sheaf (Scheme.AffineEtale.topology U) C.{u} :=
  restriction j C.{u} ⋙ (E U).inverse


/-- The actual ambient restriction to the affine basis preserves exact sequences. -/
theorem restrictToAffine_exact :
    PreservesFiniteLimits (restrictToAffine j) ∧ PreservesFiniteColimits (restrictToAffine j) := by
  letI : PreservesFiniteLimits (restriction j C.{u}) := (restriction_exact j).1
  letI : PreservesFiniteColimits (restriction j C.{u}) := (restriction_exact j).2
  unfold restrictToAffine
  exact ⟨inferInstance, inferInstance⟩

/-- Actual ambient restriction to the affine basis preserves injective sheaves. -/
theorem restrictToAffine_preservesInjectiveObjects :
    (restrictToAffine j).PreservesInjectiveObjects := by
  let L := extensionByZero j C.{u}
  letI : PreservesFiniteLimits L := (extensionByZero_exact j).1
  letI : (restriction j C.{u}).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (abelianExtensionByZeroAdjunction j)
  unfold restrictToAffine
  infer_instance

/-- The underlying section at the terminal object of the actual affine
basis is the same section as on the ambient étale open. -/
def affineSectionEquiv {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology C.{u}) :
    F.obj.obj (op (Scheme.Etale.mk j)) ≃+
      ((restrictToAffine j).obj F).obj.obj (op (baseObject R)) :=
  sectionEquiv j F

/-- Restricting to the ambient affine basis and then to a smaller open
agrees with restricting to its actual affine basis in one step. -/
def nestedRestrictionIso :
    restrictToAffine j ⋙ affineRestriction i ≅ restrictToAffine (i ≫ j) := by
  let A := restriction j C.{u}
  let B := restriction i C.{u}
  let L := (E U).inverse
  let G := (E U).functor
  let M := (E V).inverse
  let e : L ⋙ G ≅ 𝟭 _ := (E U).counitIso
  have h₁ : restrictToAffine j ⋙ affineRestriction i ≅ A ⋙ ((L ⋙ G) ⋙ (B ⋙ M)) :=
    Iso.refl _
  have h₂ : A ⋙ ((L ⋙ G) ⋙ (B ⋙ M)) ≅ A ⋙ (𝟭 _ ⋙ (B ⋙ M)) :=
    Functor.isoWhiskerLeft A (Functor.isoWhiskerRight e (B ⋙ M))
  have h₃ : A ⋙ (𝟭 _ ⋙ (B ⋙ M)) ≅ (A ⋙ B) ⋙ M :=
    Functor.isoWhiskerLeft A (Functor.leftUnitor (B ⋙ M)) ≪≫ (Functor.associator A B M).symm
  exact h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ Functor.isoWhiskerRight (restrictionCompIso i j) M

/-- Passing to the actual affine basis commutes with the unit sheaf on an open. -/
def affineUnitsIso {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :
    (restrictToAffine j).obj (KummerUnitsSheaf.fullCoordinateUnitSheaf X) ≅
      KummerUnitsSheaf.coordinateUnitSheaf U := by
  let e := (E U).inverse.mapIso (OpenEtaleUnitComparison.restrictionIso j)
  refine e ≪≫ (fullyFaithfulSheafToPresheaf
    (Scheme.AffineEtale.topology U) AddCommGrpCat.{0}).preimageIso ?_
  change (Scheme.AffineEtale.Spec U).op ⋙ KummerUnitsSheaf.fullCoordinateUnits U ≅
    KummerUnitsPresheaf.units U
  exact KummerUnitsSheaf.affineRestrictionUnitsIso U

end

end ManuscriptAudit.NestedAffineEtaleRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NestedAffineEtaleRestriction.restrictToAffine_exact,
      ``ManuscriptAudit.NestedAffineEtaleRestriction.restrictToAffine_preservesInjectiveObjects,
      ``ManuscriptAudit.NestedAffineEtaleRestriction.affineSectionEquiv,
      ``ManuscriptAudit.NestedAffineEtaleRestriction.nestedRestrictionIso,
      ``ManuscriptAudit.NestedAffineEtaleRestriction.affineUnitsIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
