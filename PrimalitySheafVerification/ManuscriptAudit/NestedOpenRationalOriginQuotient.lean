import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ClosedRationalPointUniqueRefinements
import PrimalitySheafVerification.ManuscriptAudit.ClosedRationalSkyscraperOffSupport
import PrimalitySheafVerification.ManuscriptAudit.CuspOriginGeometricDirectImage
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionQuotientExact
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionToSkyscraper
import PrimalitySheafVerification.ManuscriptAudit.RationalPointStalkConservative

/-!
# The closed rational origin quotient of nested open extensions

When the smaller open omits exactly one closed rational point of
the larger one, its extension-by-zero quotient is the actual direct
image of the constant sheaf from that point. The comparison is the
native map to the geometric skyscraper, checked on geometric stalks.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SmallEtaleBaseChange SmallEtaleGeometricBaseChange

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j] (M : C.{u})
variable {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ U) [IsClosedImmersion (s ≫ j)]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem origin_doesNotFactor (hRange : Set.range i = (Set.range s)ᶜ) :
    ¬ ∃ t : Spec (CommRingCat.of K) ⟶ V, t ≫ i = s := by
  rintro ⟨t, ht⟩
  let a : Spec (CommRingCat.of K) := default
  have h : s a ∈ Set.range i :=
    ⟨t a, by simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (CommRingCat.of K) ⟶ U => f a) ht⟩
  rw [hRange] at h
  exact h ⟨a, rfl⟩

private theorem quotient_zero_away
    (hRange : Set.range i = (Set.range s)ᶜ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (r : Spec (CommRingCat.of Ω) ⟶ X)
    (hne : r (default : Spec (CommRingCat.of Ω)) ≠
      (s ≫ j) (default : Spec (CommRingCat.of K))) :
    IsZero ((Scheme.pointSmallEtale r).sheafFiber.obj
      (cokernel (nestedOpenConstantMap i j M))) := by
  by_cases hr : ∃ t : Spec (CommRingCat.of Ω) ⟶ U, t ≫ j = r
  · obtain ⟨t, rfl⟩ := hr
    have ht : Set.range t ⊆ Set.range i := by
      rw [hRange]
      rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
      have h := congrArg (fun y : U => j y) hb.symm
      apply hne
      simpa only [Scheme.Hom.comp_apply, Subsingleton.elim a default,
        Subsingleton.elim b default] using h
    let v := IsOpenImmersion.lift i t ht
    have hv : v ≫ i = t := IsOpenImmersion.lift_fac _ _ _
    rw [← hv]
    exact nestedOpenQuotient_stalk_isZero_inside i j M v
  · exact nestedOpenQuotient_stalk_isZero_outside i j M r hr

/-- The native nested-open cokernel is the direct image of the constant
sheaf from the single closed rational point between the opens. -/
def nestedOpenQuotientRationalOriginIso
    (hRange : Set.range i = (Set.range s)ᶜ) :
    cokernel (nestedOpenConstantMap i j M) ≅
      (directImage (s ≫ j) C.{u}).obj
        ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology C.{u}).obj M) := by
  let o := s ≫ j
  let Φ := Scheme.pointSmallEtale o
  let N := (Scheme.pointSmallEtale s).sheafFiber.obj
    ((constantSheaf U.smallEtaleTopology C.{u}).obj M)
  let hs := origin_doesNotFactor i s hRange
  let f := nestedOpenQuotientToSkyscraper i j M s hs
  have hOrigin : IsIso (Φ.sheafFiber.map f) := by
    let ε := Φ.skyscraperSheafAdjunction.counit.app N
    have e : Φ.sheafFiber.map f ≫ ε = (nestedOpenQuotientStalkIso i j M s hs).hom :=
      nestedOpenQuotientToSkyscraper_stalk_comp_counit i j M s hs
    letI : IsIso ε := closedRationalPoint_skyscraperCounit_isIso o N
    letI : IsIso (Φ.sheafFiber.map f ≫ ε) := by rw [e]; infer_instance
    exact IsIso.of_isIso_comp_right _ ε
  letI : IsIso f := isIso_of_rationalOrigin_and_remaining_stalks o f hOrigin (by
    intro Ω _ _ r hne
    exact (quotient_zero_away i j M s hRange r hne).isIso
      (closedRationalSkyscraper_stalk_isZero_of_ne o r hne N) _)
  exact asIso f ≪≫ Φ.skyscraperSheafFunctor.mapIso (constantEtaleStalkIso (Scheme.pointSmallEtale s) M) ≪≫
    (rationalPointConstantDirectImageIso K o M).symm

/-- The short complex with the actual nested-open inclusion and the
actual direct image from the closed rational origin. -/
def nestedOpenRationalOriginSequence
    (hRange : Set.range i = (Set.range s)ᶜ) : ShortComplex (Sheaf X.smallEtaleTopology C.{u}) :=
  ShortComplex.mk (nestedOpenConstantMap i j M)
    (cokernel.π (nestedOpenConstantMap i j M) ≫ (nestedOpenQuotientRationalOriginIso i j M s hRange).hom)
    (by simp)

theorem nestedOpenRationalOriginSequence_shortExact
    (hRange : Set.range i = (Set.range s)ᶜ) :
    (nestedOpenRationalOriginSequence i j M s hRange).ShortExact := by
  let e : nestedOpenQuotientSequence i j M ≅ nestedOpenRationalOriginSequence i j M s hRange :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (nestedOpenQuotientRationalOriginIso i j M s hRange)
      (by simp [nestedOpenRationalOriginSequence])
      (by simp [nestedOpenRationalOriginSequence])
  exact ShortComplex.shortExact_of_iso e (nestedOpenQuotientSequence_shortExact i j M)

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientRationalOriginIso,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenRationalOriginSequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
