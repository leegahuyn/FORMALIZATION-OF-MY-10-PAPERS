import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclicOrderQuotient
import PrimalitySheafVerification.ManuscriptAudit.ProetaleHighOpenCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetalePIDUnitHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundaryAdditive

/-! The native pro-étale Kummer boundary on an actual affine PID open
is induced by the coordinate units and commutes with restriction. -/

namespace ManuscriptAudit.NativeKummerChartBoundaryPresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleMayerVietorisSite (topology sheafEquivalence siteEquivalence)
open ProetaleHighOpenCohomology (coefficient liftedObject openEquiv)
open ProetaleOpenLocalLifts (openObject)
open ProetaleUnitSheaf (unitSheaf specUnits specUnits_naturality)
open ProetaleKummerPower (power_eval)
open ProetaleKummerSequence (sequence sequence_shortExact)
open ProetaleUnitRestriction (restrictionUnitsIso)
open ProetaleCohomologyIso (cohomologyIso)
open SheafPresheafHOneBoundary SheafPresheafHOneBoundaryAdditive
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K R : Type} [Field K] [IsAlgClosed K] [CommRing R]
  {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (d : ℕ) [NeZero d] [NeZero (d : K)]

private abbrev A := AddCommGrpCat.{1}
abbrev S (X : Scheme.{0}) (d : ℕ) := (sequence X d).map (sheafEquivalence X).functor
private abbrev Y (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] :=
  liftedObject (openObject j)

include k in
private theorem shortExact : (S X d).ShortExact :=
  (sequence_shortExact k d).map_of_exact (sheafEquivalence X).functor

private abbrev coordinateUnits :
    (S X d).X₃.obj.obj (op (Y j)) ≃+ Additive Rˣ :=
  specUnits (CommRingCat.of R) ((𝟙 (Spec (CommRingCat.of R))) ≫ j)

/-- The actual native Kummer boundary from additive coordinate units. -/
def boundary : Additive Rˣ →+ (S X d).X₁.H' 1 (Y j) :=
  (boundaryAddHom (topology X) (S X d) (shortExact k d) (Y j)).comp
    (coordinateUnits j d).symm.toAddMonoidHom

set_option maxHeartbeats 4600000 in
/-- On an affine PID chart, the native boundary is onto. -/
theorem boundary_surjective [IsDomain R] [IsPrincipalIdealRing R] :
    Function.Surjective (boundary k j d) := by
  let hS := shortExact k d
  let U := Y j
  let I := (freeYoneda (topology X)).obj U
  let h := (openEquiv j (unitSheaf X) 1).trans (cohomologyIso (restrictionUnitsIso j) 1)
  have hUnit := ProetalePIDUnitHOne.HOne_subsingleton R
  have hMid : Subsingleton ((S X d).X₂.H' 1 U) :=
    ⟨fun a b ↦ h.injective (hUnit.elim _ _)⟩
  have hBoundary : Function.Surjective (boundaryAddHom (topology X) (S X d) hS U) := by
    intro t
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ I hS t (hMid.elim _ _) (n₀ := 0) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective I (S X d).X₃).surjective a
    let e := sectionEquiv (topology X) (S X d).X₃ U
    refine ⟨e f, ?_⟩
    rw [boundaryAddHom_apply]
    change (Ext.mk₀ (e.symm (e f))).comp hS.extClass rfl = t
    simpa only [Equiv.symm_apply_apply] using ha
  exact hBoundary.comp (coordinateUnits j d).symm.surjective

set_option maxHeartbeats 4200000 in
/-- The exact kernel is the subgroup of coordinate d-th powers. -/
theorem boundary_ker :
    (boundary k j d).ker = (CyclicOrderQuotient.nsmulMap (B := Additive Rˣ) d).range := by
  let e := coordinateUnits j d
  let hS := shortExact k d
  ext z
  change boundaryOfSection (topology X) (S X d) hS (Y j) (e.symm z) = 0 ↔
    ∃ w : Additive Rˣ, d • w = z
  rw [boundaryOfSection_eq_zero_iff]
  have hw (s : (S X d).X₂.obj.obj (op (Y j))) :
      (S X d).g.hom.app (op (Y j)) s = d • s :=
    power_eval (X := X) d s
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e s, ?_⟩
    have h := congrArg e ((hw s).symm.trans hs)
    simpa only [map_nsmul, AddEquiv.apply_symm_apply] using h
  · rintro ⟨w, hw'⟩
    refine ⟨e.symm w, ?_⟩
    exact (hw _).trans ((map_nsmul e.symm w d).symm.trans (congrArg e.symm hw'))

variable {T : Type} [CommRing T] (r : CommRingCat.of R ⟶ CommRingCat.of T)
  [IsOpenImmersion (Spec.map r)]

/-- The actual chart arrow, before taking its coordinate restriction. -/
def chartArrow : openObject (Spec.map r ≫ j) ⟶ openObject j :=
  MorphismProperty.Over.homMk (Spec.map r) (by
    change Spec.map r ≫ (𝟙 (Spec (CommRingCat.of R)) ≫ j) =
      𝟙 (Spec (CommRingCat.of T)) ≫ (Spec.map r ≫ j)
    simp only [Category.id_comp])

set_option maxHeartbeats 5200000 in
/-- The native cohomology restriction is induced by the literal ring unit map. -/
theorem boundary_natural :
    (boundary k (Spec.map r ≫ j) d).comp (ringUnits.map r).hom =
      (((S X d).X₁.cohomologyPresheaf 1).map ((siteEquivalence X).functor.map (chartArrow j r)).op).hom.comp
        (boundary k j d) := by
  apply AddMonoidHom.ext
  intro u
  let U := Y j
  let V := Y (Spec.map r ≫ j)
  let e := coordinateUnits j d
  let e' := coordinateUnits (Spec.map r ≫ j) d
  let hS := shortExact k d
  let a := (siteEquivalence X).functor.map (chartArrow j r)
  change boundaryOfSection (topology X) (S X d) hS V (e'.symm ((ringUnits.map r) u)) =
    ((S X d).X₁.cohomologyPresheaf 1).map a.op
      (boundaryOfSection (topology X) (S X d) hS U (e.symm u))
  rw [boundaryOfSection_restrict]
  congr 1
  apply e'.injective
  rw [AddEquiv.apply_symm_apply]
  have h := specUnits_naturality r ((𝟙 (Spec (CommRingCat.of R))) ≫ j) (e.symm u)
  have h' : e' ((S X d).X₃.obj.map a.op (e.symm u)) = (ringUnits.map r) (e (e.symm u)) := by
    first
    | exact h
    | simpa only [e, e', coordinateUnits, chartArrow, Category.id_comp] using h
  simpa only [AddEquiv.apply_symm_apply] using h'.symm

end
end ManuscriptAudit.NativeKummerChartBoundaryPresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeKummerChartBoundaryPresentation.boundary_surjective,
      ``ManuscriptAudit.NativeKummerChartBoundaryPresentation.boundary_ker,
      ``ManuscriptAudit.NativeKummerChartBoundaryPresentation.boundary_natural] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
