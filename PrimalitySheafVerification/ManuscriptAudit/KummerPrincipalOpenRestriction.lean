import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeUnitSections
import PrimalitySheafVerification.ManuscriptAudit.NormalLocalizationUnitRoots
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! On a PID affine étale open of an arbitrary K-scheme, an actual Kummer
cohomology class is detected on any nonempty principal open. -/

namespace ManuscriptAudit.KummerPrincipalOpenRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open KummerRelativeFull KummerRelativeUnitSections KummerUnitsSheaf
open OpenEtaleExtension SheafPresheafHOneBoundary

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C := AddCommGrpCat.{0}

variable {K R : Type} [Field K] [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

private def restrictedUnitsIso :
    (restriction j C).obj (fullCoordinateUnitSheaf X) ≅
      fullCoordinateUnitSheaf (Spec (CommRingCat.of R)) := by
  apply (fullyFaithfulSheafToPresheaf _ C).preimageIso
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V f; rfl)

private theorem unitTerm_HOne_subsingleton (d : ℕ) :
    Subsingleton ((sequence X d).X₂.H' 1 (Scheme.Etale.mk j)) := by
  let J := (Spec (CommRingCat.of R)).smallEtaleTopology
  let F := (sequence X d).X₂
  let e := (restriction j C).mapIso (unitsIso (X := X) d).symm ≪≫ restrictedUnitsIso j
  let h := openCohomologyPresheafEquiv j F 1
  let g := ((Sheaf.functorH J 1).mapIso e).addCommGroupIsoToAddEquiv
  have hR := KummerUnitsSheaf.unitHOne_subsingleton_of_pid R
  exact ⟨fun x y => h.injective (g.injective (hR.allEq _ _))⟩

include k in
private theorem boundary_surjective (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    Function.Surjective (boundaryOfSection X.smallEtaleTopology (sequence X d)
        (sequence_shortExact k d hd) (Scheme.Etale.mk j)) := by
  let S := sequence X d
  let hS := sequence_shortExact k d hd
  let J := X.smallEtaleTopology
  let U := Scheme.Etale.mk j
  letI := unitTerm_HOne_subsingleton j d
  intro c
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ ((freeYoneda J).obj U) hS c
    (Subsingleton.elim _ _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) S.X₃).surjective z
  refine ⟨sectionEquiv J S.X₃ U f, ?_⟩
  change (Ext.mk₀ ((sectionEquiv J S.X₃ U).symm (sectionEquiv J S.X₃ U f))).comp
    hS.extClass rfl = _
  rw [Equiv.symm_apply_apply]
  exact hz

variable (s : R)
private abbrev locHom : CommRingCat.of R ⟶ CommRingCat.of (Localization.Away s) :=
  CommRingCat.ofHom (algebraMap R (Localization.Away s))

private instance locOpen : IsOpenImmersion (Spec.map (locHom s)) :=
  IsOpenImmersion.of_isLocalization (S := Localization.Away s) s

include k in
/-- The actual degree-one Kummer restriction to a nonempty principal open is injective. -/
theorem restriction_firstTerm_injective [IsIntegrallyClosed R] (hs : s ≠ 0)
    (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    Function.Injective (((sequence X d).X₁.cohomologyPresheaf 1).map
      (chartArrow (locHom s) j).op) := by
  let J := X.smallEtaleTopology
  let S := sequence X d
  let hS := sequence_shortExact k d hd
  let r := locHom s
  let U := Scheme.Etale.mk j
  let j' := Spec.map r ≫ j
  let V := Scheme.Etale.mk j'
  let a := chartArrow r j
  apply (injective_iff_map_eq_zero _).2
  intro c hc
  obtain ⟨v, rfl⟩ := boundary_surjective k j d hd c
  rw [boundaryOfSection_restrict J S hS a v] at hc
  obtain ⟨w, hw⟩ := (boundaryOfSection_eq_zero_iff J S hS V _).mp hc
  let EU := coordinateUnitsIso d j
  let EV := coordinateUnitsIso d j'
  have hwr : (EV.hom w).toMul ^ d =
      Units.map (algebraMap R (Localization.Away s)).toMonoidHom (EU.hom v).toMul := by
    have h₁ := congrArg (fun x : S.X₂.obj.obj (op V) => EV.hom x)
      ((coordinateUnitsIso_power w).symm.trans hw)
    have h₂ := congrArg (fun f : S.X₂.obj.obj (op U) ⟶
        AddCommGrpCat.of (Additive (Localization.Away s)ˣ) => f v)
      (coordinateUnitsIso_restrict d r j)
    have h₃ : d • EV.hom w = (ringUnits.map r) (EU.hom v) := by
      rw [← map_nsmul]
      exact h₁.trans h₂
    exact congrArg Additive.toMul h₃
  obtain ⟨u, hu, _⟩ := NormalLocalizationUnitRoots.unit_root_extends R s hs d hd _ _ hwr
  refine (boundaryOfSection_eq_zero_iff J S hS U v).mpr ⟨EU.inv (Additive.ofMul u), ?_⟩
  apply (ConcreteCategory.injective_of_mono EU.hom)
  rw [coordinateUnitsIso_power, map_nsmul]
  have h : EU.hom (EU.inv (Additive.ofMul u)) = Additive.ofMul u :=
    Iso.inv_hom_id_apply EU _
  rw [h, ← Additive.ofMul_pow]
  exact congrArg Additive.ofMul hu

include k in
/-- The same restriction is injective for the literal constant coefficient sheaf. -/
theorem restriction_constant_injective [IsIntegrallyClosed R] (hs : s ≠ 0)
    (d : ℕ) (hd : 0 < d) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d] :
    Function.Injective ((((constantSheaf X.smallEtaleTopology C).obj
        (KummerConstantCoefficients.coefficientGroup K d)).cohomologyPresheaf 1).map
      (chartArrow (locHom s) j).op) := by
  let a := chartArrow (locHom s) j
  let e := (Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology 1).mapIso
    (firstIso (d := d) k)
  intro x y h
  let U := op (Scheme.Etale.mk j)
  let V := op (Scheme.Etale.mk (Spec.map (locHom s) ≫ j))
  apply ConcreteCategory.injective_of_mono (e.hom.app U)
  apply restriction_firstTerm_injective k j s hs d hd
  have hn := e.hom.naturality a.op
  have hx := ConcreteCategory.congr_hom hn x
  have hy := ConcreteCategory.congr_hom hn y
  exact hx.symm.trans ((congrArg (e.hom.app V) h).trans hy)

end
end ManuscriptAudit.KummerPrincipalOpenRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerPrincipalOpenRestriction.restriction_firstTerm_injective,
      ``ManuscriptAudit.KummerPrincipalOpenRestriction.restriction_constant_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
