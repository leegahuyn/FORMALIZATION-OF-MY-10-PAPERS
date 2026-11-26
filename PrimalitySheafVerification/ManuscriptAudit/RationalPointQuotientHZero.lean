import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZeroEvaluation
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenRationalOriginQuotient

/-!
# Degree-zero surjectivity for the native rational-point quotient

When an open immersion omits exactly one closed separably closed point,
the larger open can be taken to be the whole scheme. In the checked
nested-open quotient, the resulting map from constants onto the closed
direct image is surjective on global cohomology.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GeometricSkyscraperCohomology SmallEtaleGeometricBaseChange

universe u

noncomputable section

attribute [local instance] etaleSiteHasExt

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

/-- Extending along the identity recovers the original abelian sheaf. -/
def extensionByZeroIdIso (X : Scheme.{u}) :
    extensionByZero (𝟙 X) C.{u} ≅ 𝟭 (Sheaf X.smallEtaleTopology C.{u}) := by
  letI := postcomposeContinuous (𝟙 X)
  let e : etalePostcompose (𝟙 X) ≅ 𝟭 X.Etale :=
    MorphismProperty.Over.mapId (P := @AlgebraicGeometry.Etale) ⊤ X
  let r : restriction (𝟙 X) C.{u} ≅ 𝟭 (Sheaf X.smallEtaleTopology C.{u}) :=
    Functor.sheafPushforwardContinuousId' (eF'' := e) C.{u} X.smallEtaleTopology
  exact ((abelianExtensionByZeroAdjunction (𝟙 X)).ofNatIsoRight r).leftAdjointUniq
    Adjunction.id

private theorem cokernelProjection_isIso_of_eq_zero {D : Type*} [Category* D]
    [HasZeroMorphisms D] [HasCokernels D] {A B : D} (f : A ⟶ B) (h : f = 0) :
    IsIso (cokernel.π f) := by
  subst f
  exact (cokernelZeroIsoTarget (X := A) (Y := B)).isIso_inv

variable {V X : Scheme.{u}} (i : V ⟶ X) [IsOpenImmersion i]
variable (M : C.{u}) {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion (s ≫ 𝟙 X)]

/-- The exact native quotient map for a one-point complement is onto on degree-zero cohomology. -/
theorem rationalPointQuotient_HZero_surjective
    (hRange : Set.range i = (Set.range s)ᶜ) :
    Function.Surjective
      (Sheaf.H.map (nestedOpenRationalOriginSequence i (𝟙 X) M s hRange).g 0) := by
  let Φ := Scheme.pointSmallEtale (s ≫ 𝟙 X)
  let L := Φ.sheafFiber (A := C.{u})
  let F := (constantSheaf X.smallEtaleTopology C.{u}).obj M
  let Q := nestedOpenRationalOriginSequence i (𝟙 X) M s hRange
  let n := nestedOpenConstantMap i (𝟙 X) M
  let b := (extensionByZeroIdIso X).app F
  let c := rationalPointConstantDirectImageIso K (s ≫ 𝟙 X) M
  let f : F ⟶ Φ.skyscraperSheaf M := b.inv ≫ Q.g ≫ c.hom
  have hOutside : ¬ ∃ t : Spec (CommRingCat.of K) ⟶ V,
      t ≫ (i ≫ 𝟙 X) = s ≫ 𝟙 X := by
    rintro ⟨t, ht⟩
    have ht' : t ≫ i = s := by simpa only [Category.comp_id] using ht
    let a : Spec (CommRingCat.of K) := default
    have ha : s a ∈ Set.range i :=
      ⟨t a, by simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun g : Spec (CommRingCat.of K) ⟶ X => g a) ht'⟩
    rw [hRange] at ha
    exact ha ⟨a, rfl⟩
  have hz : L.map n = 0 :=
    (extensionByZero_stalk_isZero (i ≫ 𝟙 X) (s ≫ 𝟙 X) hOutside
      ((constantSheaf V.smallEtaleTopology C.{u}).obj M)).eq_of_src _ _
  letI : IsIso (L.map (cokernel.π n)) := by
    let a := PreservesCokernel.iso L n
    letI : IsIso (L.map (cokernel.π n) ≫ a.hom) := by
      rw [PreservesCokernel.π_iso_hom]
      exact cokernelProjection_isIso_of_eq_zero (L.map n) hz
    exact IsIso.of_isIso_comp_right _ a.hom
  letI : IsIso (L.map Q.g) := by
    change IsIso (L.map (cokernel.π n ≫
      (nestedOpenQuotientRationalOriginIso i (𝟙 X) M s hRange).hom))
    rw [Functor.map_comp]
    infer_instance
  letI : IsIso (Φ.skyscraperSheafAdjunction.counit.app M) :=
    closedRationalPoint_skyscraperCounit_isIso (s ≫ 𝟙 X) M
  letI : IsIso (L.map f) := by
    dsimp only [f, L]
    simp only [Functor.map_comp]
    infer_instance
  have hf : Function.Surjective (Sheaf.H.map f 0) :=
    HZero_surjective_of_stalkAdjoint_iso Φ M M f inferInstance
  let e := ((Sheaf.functorH X.smallEtaleTopology 0).mapIso c).addCommGroupIsoToAddEquiv
  intro y
  obtain ⟨x, hx⟩ := hf (e y)
  refine ⟨Sheaf.H.map b.inv 0 x, e.injective ?_⟩
  change Sheaf.H.map c.hom 0 (Sheaf.H.map Q.g 0 (Sheaf.H.map b.inv 0 x)) = e y
  simpa only [f, Sheaf.H.map_comp_apply] using hx

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.extensionByZeroIdIso,
      ``ManuscriptAudit.OpenEtaleExtension.rationalPointQuotient_HZero_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
