import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import PrimalitySheafVerification.ManuscriptAudit.KummerUnitsSheaf

/-!
# Units on the full small étale site

The units of the global functions on a small étale object are represented,
after forgetting the group structure, by the Laurent polynomial spectrum.
On affine étale objects they recover the explicit affine coordinate units.
-/

namespace ManuscriptAudit.KummerUnitsSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsPresheaf

noncomputable section

private abbrev laurentRing : CommRingCat.{0} := CommRingCat.of (LaurentPolynomial ℤ)

private def intAlgHomEquiv (R S : CommRingCat.{0}) : (R ⟶ S) ≃ (R →ₐ[ℤ] S) where
  toFun f :=
    { toRingHom := f.hom
      commutes' z := by
        change f.hom (z : R) = (z : S)
        exact map_intCast f.hom z }
  invFun f := CommRingCat.ofHom f.toRingHom
  left_inv f := CommRingCat.hom_ext rfl
  right_inv f := AlgHom.ext fun _ => rfl

private def etaleUnderlying (X : Scheme.{0}) : X.Etale ⥤ Scheme.{0} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private instance (X : Scheme.{0}) :
    (etaleUnderlying X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology := by
  let I := Scheme.etaleTopology.over X
  let F := Scheme.Etale.forget X
  letI : F.IsContinuous X.smallEtaleTopology I := by
    letI : RepresentablyFlat F := flat_of_preservesFiniteLimits F
    let P : MorphismProperty Scheme.{0} := @Etale
    letI : P.IsStableUnderComposition := by
      constructor
      intro Y Z W f g hf hg
      letI : Etale f := hf
      letI : Etale g := hg
      exact Etale.etale_comp f g
    letI : P.IsStableUnderBaseChange := Etale.etale_isStableUnderBaseChange
    letI : P.RespectsIso := by
      apply MorphismProperty.respectsIso_of_isStableUnderComposition
      intro Y Z f hf
      letI : IsIso f := hf
      exact (inferInstance : Etale f)
    letI : F.LocallyCoverDense I :=
      Scheme.locallyCoverDense_of_le X (P := P) (Q := P) le_rfl
    rw [Functor.isContinuous_iff_coverPreserving]
    exact Functor.coverPreserving_restrictedTopology F I
  exact Functor.isContinuous_comp F (Over.forget X) _ I _

/-- The covariant functor taking units, written additively. -/
def ringUnits : CommRingCat.{0} ⥤ AddCommGrpCat.{0} where
  obj R := AddCommGrpCat.of (Additive Rˣ)
  map f := AddCommGrpCat.ofHom (Units.map f.hom.toMonoidHom).toAdditive
  map_id _ := AddCommGrpCat.ext fun _ => Additive.ext (Units.ext rfl)
  map_comp _ _ := AddCommGrpCat.ext fun _ => Additive.ext (Units.ext rfl)

/-- The presheaf of units of global regular functions on all small étale schemes. -/
def fullCoordinateUnits (X : Scheme.{0}) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (etaleUnderlying X).op ⋙ Scheme.Γ ⋙ ringUnits

private def gammaHomEquiv (Y : Scheme.{0}) :
    (Y ⟶ Spec laurentRing) ≃ (laurentRing ⟶ Scheme.Γ.obj (op Y)) :=
  ((ΓSpec.adjunction.homEquiv Y (op laurentRing)).symm).trans
    { toFun := fun f => f.unop
      invFun := fun f => f.op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem gammaHomEquiv_natural {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : Z ⟶ Spec laurentRing) :
    gammaHomEquiv Y (f ≫ h) = gammaHomEquiv Z h ≫ f.appTop := by
  have e := ΓSpec.adjunction.homEquiv_naturality_left_symm f h
  exact congrArg (fun k : Scheme.Γ.rightOp.obj Y ⟶ op laurentRing => k.unop) e

private def globalUnitsEquiv (Y : Scheme.{0}) :
    (Y ⟶ Spec laurentRing) ≃ Additive (Scheme.Γ.obj (op Y))ˣ :=
  (gammaHomEquiv Y).trans ((intAlgHomEquiv laurentRing _).trans
    ((LaurentUnitRepresentation.laurentAlgHomEquivUnits ℤ _).trans Additive.ofMul))

private theorem globalUnitsEquiv_natural {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : Z ⟶ Spec laurentRing) :
    globalUnitsEquiv Y (f ≫ h) =
      Additive.ofMul (Units.map f.appTop.hom.toMonoidHom (globalUnitsEquiv Z h).toMul) := by
  apply Additive.ext
  apply Units.ext
  simp only [globalUnitsEquiv, Equiv.trans_apply, gammaHomEquiv_natural,
    LaurentUnitRepresentation.laurentAlgHomEquivUnits_val]
  rfl

/-- Forgetting the additive group structure identifies the units presheaf
with the restriction of the representable Laurent polynomial spectrum. -/
def fullUnitsUnderlyingIso (X : Scheme.{0}) :
    (etaleUnderlying X).op ⋙ yoneda.obj (Spec laurentRing) ≅
      fullCoordinateUnits X ⋙ forget AddCommGrpCat.{0} :=
  NatIso.ofComponents (fun U => (globalUnitsEquiv ((etaleUnderlying X).obj U.unop)).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro h
    exact globalUnitsEquiv_natural ((etaleUnderlying X).map f.unop) h)

/-- The presheaf of units satisfies descent on the full small étale site. -/
theorem fullCoordinateUnits_isSheaf (X : Scheme.{0}) :
    Presheaf.IsSheaf X.smallEtaleTopology (fullCoordinateUnits X) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{0})
  apply (Presheaf.isSheaf_of_iso_iff (fullUnitsUnderlyingIso X)).mp
  apply (etaleUnderlying X).op_comp_isSheaf_of_isSheaf _ Scheme.etaleTopology
  have h : Presheaf.IsSheaf Scheme.proetaleTopology (yoneda.obj (Spec laurentRing)) := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.proetaleTopology) (yoneda.obj (Spec laurentRing))
  exact Presheaf.IsSheaf.of_le Scheme.etaleTopology_le_proetaleTopology h

/-- The unit sheaf on the full small étale site. -/
def fullCoordinateUnitSheaf (X : Scheme.{0}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{0} :=
  ⟨fullCoordinateUnits X, fullCoordinateUnits_isSheaf X⟩

/-- On each affine étale object, the full unit sheaf gives the units of the
actual coordinate ring. -/
def affineRestrictionUnitsIso (X : Scheme.{0}) :
    (Scheme.AffineEtale.Spec X).op ⋙ fullCoordinateUnits X ≅ units X :=
  NatIso.ofComponents (fun U => ringUnits.mapIso (Scheme.ΓSpecIso (coordinateRing U.unop))) (by
    intro U V f
    let g := f.unop.left.unop
    change ringUnits.map (Spec.map g).appTop ≫ ringUnits.map (Scheme.ΓSpecIso _).hom =
      ringUnits.map (Scheme.ΓSpecIso _).hom ≫ ringUnits.map g
    rw [← ringUnits.map_comp, ← ringUnits.map_comp, Scheme.ΓSpecIso_naturality])


end

end ManuscriptAudit.KummerUnitsSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerUnitsSheaf.fullCoordinateUnits_isSheaf,
      ``ManuscriptAudit.KummerUnitsSheaf.affineRestrictionUnitsIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
