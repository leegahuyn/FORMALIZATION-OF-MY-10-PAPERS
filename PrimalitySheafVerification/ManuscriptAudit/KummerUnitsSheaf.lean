import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import PrimalitySheafVerification.ManuscriptAudit.KummerSheafSequence
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitRepresentation

/-!
# Coordinate units form a sheaf on the small affine étale site

The underlying presheaf is the restriction of the presheaf represented by
the spectrum of the integer Laurent polynomial ring. Subcanonicity and
continuity of the restriction establish descent for units.
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

private def specUnitsEquiv (R : CommRingCat.{0}) :
    (Spec R ⟶ Spec laurentRing) ≃ Additive Rˣ :=
  Spec.homEquiv.trans ((intAlgHomEquiv laurentRing R).trans
    ((LaurentUnitRepresentation.laurentAlgHomEquivUnits ℤ R).trans Additive.ofMul))

private theorem specUnitsEquiv_natural {R S : CommRingCat.{0}} (f : R ⟶ S)
    (h : Spec R ⟶ Spec laurentRing) :
    specUnitsEquiv S (Spec.map f ≫ h) =
      Additive.ofMul (Units.map f.hom.toMonoidHom (specUnitsEquiv R h).toMul) := by
  apply Additive.ext
  apply Units.ext
  simp only [specUnitsEquiv, Equiv.trans_apply, Spec.homEquiv_apply,
    Spec.preimage_comp, Spec.preimage_map, LaurentUnitRepresentation.laurentAlgHomEquivUnits_val]
  rfl

private def etaleUnderlying (X : Scheme.{0}) : X.Etale ⥤ Scheme.{0} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private instance (X : Scheme.{0}) :
    (etaleUnderlying X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology := by
  let I := Scheme.etaleTopology.over X
  let F := Scheme.Etale.forget X
  letI : F.IsContinuous X.smallEtaleTopology I := by
    change (MorphismProperty.Over.forget @Etale ⊤ X).IsContinuous
      ((MorphismProperty.Over.forget @Etale ⊤ X).restrictedTopology I) I
    letI : RepresentablyFlat (MorphismProperty.Over.forget @Etale ⊤ X) :=
      flat_of_preservesFiniteLimits _
    rw [Functor.isContinuous_iff_coverPreserving]
    exact Functor.coverPreserving_restrictedTopology _ _
  exact Functor.isContinuous_comp F (Over.forget X) _ I _

private def affineUnderlying (X : Scheme.{0}) : X.AffineEtale ⥤ Scheme.{0} :=
  Scheme.AffineEtale.Spec X ⋙ etaleUnderlying X

private instance (X : Scheme.{0}) :
    (affineUnderlying X).IsContinuous (Scheme.AffineEtale.topology X) Scheme.etaleTopology :=
  Functor.isContinuous_comp (Scheme.AffineEtale.Spec X) (etaleUnderlying X)
    _ X.smallEtaleTopology _

/-- On the small affine étale site, the units presheaf is the restriction of
the presheaf of morphisms into the spectrum of the Laurent polynomial ring,
after forgetting the additive group structure. -/
def unitsUnderlyingIso (X : Scheme.{0}) :
    (affineUnderlying X).op ⋙ yoneda.obj (Spec laurentRing) ≅
      units X ⋙ forget AddCommGrpCat.{0} :=
  NatIso.ofComponents (fun U => (specUnitsEquiv (coordinateRing U.unop)).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro h
    exact specUnitsEquiv_natural f.unop.left.unop h)

/-- Coordinate units form an additive-group-valued sheaf on the small affine
étale site. -/
theorem units_isSheaf (X : Scheme.{0}) :
    Presheaf.IsSheaf (Scheme.AffineEtale.topology X) (units X) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{0})
  apply (Presheaf.isSheaf_of_iso_iff _ (unitsUnderlyingIso X)).mp
  apply (affineUnderlying X).op_comp_isSheaf_of_isSheaf _ Scheme.etaleTopology
  apply Presheaf.IsSheaf.of_le Scheme.etaleTopology_le_proetaleTopology
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The coordinate-unit sheaf, using its explicit sections on affine objects. -/
def coordinateUnitSheaf (X : Scheme.{0}) :
    Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{0} :=
  ⟨units X, units_isSheaf X⟩

/-- Sheafification identifies canonically with the coordinate-unit sheaf. -/
def coordinateUnitSheafIso (X : Scheme.{0}) :
    coordinateUnitSheaf X ≅ KummerSheafSequence.unitSheaf X :=
  sheafificationIso (coordinateUnitSheaf X)

end

end ManuscriptAudit.KummerUnitsSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerUnitsSheaf.unitsUnderlyingIso,
      ``ManuscriptAudit.KummerUnitsSheaf.units_isSheaf,
      ``ManuscriptAudit.KummerUnitsSheaf.coordinateUnitSheafIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
