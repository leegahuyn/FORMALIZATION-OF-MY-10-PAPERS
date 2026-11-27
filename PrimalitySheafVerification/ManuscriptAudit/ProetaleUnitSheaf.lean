import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! Units of global functions give the actual pro-étale sheaf of
multiplicative units, including on nonaffine objects. -/

namespace ManuscriptAudit.ProetaleUnitSheaf

open AlgebraicGeometry CategoryTheory Opposite
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev laurentRing : CommRingCat.{0} := CommRingCat.of (LaurentPolynomial ℤ)

private def intAlgHomEquiv (R S : CommRingCat.{0}) : (R ⟶ S) ≃ (R →ₐ[ℤ] S) where
  toFun f :=
    { toRingHom := f.hom
      commutes' z := map_intCast f.hom z }
  invFun f := CommRingCat.ofHom f.toRingHom
  left_inv f := CommRingCat.hom_ext rfl
  right_inv f := AlgHom.ext fun _ ↦ rfl

private def gammaHomEquiv (Y : Scheme.{0}) :
    (Y ⟶ Spec laurentRing) ≃ (laurentRing ⟶ Scheme.Γ.obj (op Y)) :=
  ((ΓSpec.adjunction.homEquiv Y (op laurentRing)).symm).trans
    { toFun := fun f ↦ f.unop
      invFun := fun f ↦ f.op
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem gammaHomEquiv_natural {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : Z ⟶ Spec laurentRing) :
    gammaHomEquiv Y (f ≫ h) = gammaHomEquiv Z h ≫ f.appTop := by
  have e := ΓSpec.adjunction.homEquiv_naturality_left_symm f h
  exact congrArg (fun k : Scheme.Γ.rightOp.obj Y ⟶ op laurentRing ↦ k.unop) e

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

abbrev underlying (X : Scheme.{0}) : X.ProEt ⥤ Scheme.{0} :=
  Scheme.ProEt.forget X ⋙ Over.forget X

/-- The units presheaf on the native pro-étale site. -/
def units (X : Scheme.{0}) : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (underlying X).op ⋙ Scheme.Γ ⋙ ringUnits

/-- Representability by the Laurent polynomial spectrum on the native site. -/
def underlyingIso (X : Scheme.{0}) :
    (underlying X).op ⋙ yoneda.obj (Spec laurentRing) ≅
      units X ⋙ forget AddCommGrpCat.{0} :=
  NatIso.ofComponents (fun U ↦ (globalUnitsEquiv ((underlying X).obj U.unop)).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro h
    exact globalUnitsEquiv_natural ((underlying X).map f.unop) h)

/-- Units of global functions satisfy actual pro-étale descent. -/
theorem units_isSheaf (X : Scheme.{0}) :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (units X) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{0})
  apply (Presheaf.isSheaf_of_iso_iff (underlyingIso X)).mp
  apply (underlying X).op_comp_isSheaf_of_isSheaf _ Scheme.proetaleTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.proetaleTopology) (yoneda.obj (Spec laurentRing))

/-- The native units sheaf in the coefficient universe of actual cohomology. -/
def unitSheaf (X : Scheme.{0}) : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj ⟨units X, units_isSheaf X⟩

variable {X : Scheme.{0}}

/-- The units on a chart given by a spectrum are those of its coordinate ring. -/
def specUnits (A : CommRingCat.{0}) (g : Spec A ⟶ X) [WeaklyEtale g] :
    (unitSheaf X).obj.obj (op (Scheme.ProEt.mk g)) ≃+ Additive Aˣ :=
  AddEquiv.ulift.trans ((ringUnits.mapIso (Scheme.ΓSpecIso A)).addCommGroupIsoToAddEquiv)

/-- The coordinate restriction along an actual arrow of spectra is the
usual map of units of the corresponding ring homomorphism. -/
theorem specUnits_naturality {A B : CommRingCat.{0}} (f : A ⟶ B)
    (g : Spec A ⟶ X) [WeaklyEtale g] [WeaklyEtale (Spec.map f ≫ g)]
    (s : (unitSheaf X).obj.obj (op (Scheme.ProEt.mk g))) :
    specUnits B (Spec.map f ≫ g)
        ((unitSheaf X).obj.map (MorphismProperty.Over.homMk (Spec.map f) rfl).op s) =
      Additive.ofMul (Units.map f.hom.toMonoidHom (specUnits A g s).toMul) := by
  have h : ringUnits.map (Spec.map f).appTop ≫ (ringUnits.mapIso (Scheme.ΓSpecIso B)).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso A)).hom ≫ ringUnits.map f := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  exact ConcreteCategory.congr_hom h s.down

end
end ManuscriptAudit.ProetaleUnitSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleUnitSheaf.units_isSheaf,
      ``ManuscriptAudit.ProetaleUnitSheaf.specUnits_naturality] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
