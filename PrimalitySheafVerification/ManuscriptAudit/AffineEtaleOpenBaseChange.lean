import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedBaseChangeLine

/-! Actual affine small étale cover and overlap maps along a base open,
with the literal base-change squares on both Čech projections. -/

namespace ManuscriptAudit.AffineEtaleOpenBaseChange

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction
open FlatTwistedBaseChangeLine TwistedTensorEqualizer

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] doubleEtale

variable (A B S : Type) [CommRing A] [CommRing B] [CommRing S]
variable [Algebra A B] [Algebra A S] [Algebra.Etale A B] [Algebra.Etale S (Cover A B S)]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (j A S)]

private abbrev h := (Algebra.TensorProduct.includeRight : B →ₐ[A] Cover A B S)

/-- The comparison map from the base-changed actual singleton cover. -/
def coverMap :
    (affinePostcompose (j A S)).obj (ofAlgebra S (Cover A B S)) ⟶ ofAlgebra A B :=
  MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom (h A B S).toRingHom).op trivial (by
    change Spec.map (CommRingCat.ofHom (h A B S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Cover A B S))) ≫ j A S
    unfold j
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact ((h A B S).commutes a).trans (IsScalarTower.algebraMap_apply A S (Cover A B S) a))

/-- The comparison map from the base-changed genuine double overlap. -/
def doubleMap :
    (affinePostcompose (j A S)).obj (ofAlgebra S (Double S (Cover A B S))) ⟶
      ofAlgebra A (Double A B) :=
  MorphismProperty.CostructuredArrow.homMk
    (CommRingCat.ofHom (overlapMap A B S).toRingHom).op trivial (by
    change Spec.map (CommRingCat.ofHom (overlapMap A B S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Double A B))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Double S (Cover A B S)))) ≫ j A S
    unfold j
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact ((overlapMap A B S).commutes a).trans
      (IsScalarTower.algebraMap_apply A S (Double S (Cover A B S)) a))


/-- The map from the affine base object of the open to the ambient base. -/
def baseMap :
    (affinePostcompose (j A S)).obj (baseObject S) ⟶ baseObject A :=
  MorphismProperty.CostructuredArrow.homMk
    (CommRingCat.ofHom (algebraMap A S)).op trivial (by
      change j A S ≫ 𝟙 (X A) = 𝟙 (X S) ≫ j A S
      rw [Category.comp_id, Category.id_comp])

/-- The original singleton cover maps to the actual base-changed singleton cover. -/
theorem coverSquare :
    coverMap A B S ≫ coverArrow A B =
      (affinePostcompose (j A S)).map (coverArrow S (Cover A B S)) ≫ baseMap A S := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  apply CommRingCat.hom_ext
  ext a
  change h A B S (algebraMap A B a) =
    algebraMap S (Cover A B S) (algebraMap A S a)
  exact ((h A B S).commutes a).trans (IsScalarTower.algebraMap_apply A S (Cover A B S) a)

/-- Actual first projection of the overlap commutes with restriction. -/
theorem firstSquare :
    doubleMap A B S ≫ firstProjection A B =
      (affinePostcompose (j A S)).map (firstProjection S (Cover A B S)) ≫ coverMap A B S := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  ext b
  change overlapMap A B S (first A B b) =
    first S (Cover A B S) ((1 : S) ⊗ₜ[A] b)
  exact overlapMap_first A B S b

/-- Actual second projection of the overlap commutes with restriction. -/
theorem secondSquare :
    doubleMap A B S ≫ secondProjection A B =
      (affinePostcompose (j A S)).map (secondProjection S (Cover A B S)) ≫ coverMap A B S := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  ext b
  change overlapMap A B S (second A B b) =
    second S (Cover A B S) ((1 : S) ⊗ₜ[A] b)
  exact overlapMap_second A B S b

end

end ManuscriptAudit.AffineEtaleOpenBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleOpenBaseChange.coverSquare,
      ``ManuscriptAudit.AffineEtaleOpenBaseChange.firstSquare,
      ``ManuscriptAudit.AffineEtaleOpenBaseChange.secondSquare] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
