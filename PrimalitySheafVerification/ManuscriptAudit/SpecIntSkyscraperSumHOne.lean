import Lean.Util.CollectAxioms
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.RingTheory.PrincipalIdealDomain
import PrimalitySheafVerification.ManuscriptAudit.ClosedPointCoproduct
import PrimalitySheafVerification.ManuscriptAudit.FiniteSkyscraperSumHOne
import PrimalitySheafVerification.ManuscriptAudit.GenericPointSupportDetection

/-!
# First cohomology of arbitrary closed-prime sums on Spec ℤ

A section of the actual skyscraper coproduct vanishes near the generic
point because its generic stalk is zero. The neighborhood has finite
complement. The remaining coordinates can be lifted one at a time and
added, and the summand projections distinguish sections by their stalks.
Thus every restriction is surjective and native H¹ vanishes.
-/

namespace ManuscriptAudit.SpecIntSkyscraperSumHOne

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.SkyscraperHOne
open ManuscriptAudit.FiniteSkyscraperSumHOne ManuscriptAudit.ClosedPointSupportDetection
open scoped BigOperators ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}
private abbrev X₀ := TopCat.of (PrimeSpectrum ℤ)

private abbrev part {X : TopCat.{0}} {P : Set X} (A : P → G) (p : P) :
    AbelianSheaf X := pointSummand (p : X) (A p)

local instance part_hasCoproduct {X : TopCat.{0}} {P : Set X} (A : P → G) :
    HasCoproduct (part A) := abelianSheaf_hasDiscreteColimit X (Discrete.functor (part A))

/-- The coproduct in the category of native abelian sheaves. -/
def pointCoproduct {X : TopCat.{0}} {P : Set X} (A : P → G) : AbelianSheaf X :=
  ∐ part A

private abbrev inclusion {X : TopCat.{0}} {P : Set X} (A : P → G) (p : P) :
    part A p ⟶ pointCoproduct A := Sigma.ι (part A) p

private def legs {X : TopCat.{0}} {P : Set X} (A : P → G) (p q : P) :
    part A q ⟶ part A p := by
  classical exact if h : q = p then eqToHom (congrArg (part A) h) else 0

private def projection {X : TopCat.{0}} {P : Set X} (A : P → G) (p : P) :
    pointCoproduct A ⟶ part A p := Sigma.desc (legs A p)

private theorem inclusion_projection_self {X : TopCat.{0}} {P : Set X} (A : P → G) (p : P) :
    inclusion A p ≫ projection A p = 𝟙 _ := by
  change Sigma.ι (part A) p ≫ Sigma.desc (legs A p) = _
  rw [Sigma.ι_desc]
  simp [legs]

private theorem inclusion_projection_ne {X : TopCat.{0}} {P : Set X} (A : P → G) {p q : P}
    (h : q ≠ p) : inclusion A q ≫ projection A p = 0 := by
  change Sigma.ι (part A) q ≫ Sigma.desc (legs A p) = _
  rw [Sigma.ι_desc]
  simp [legs, h]

private abbrev stalkAt {X : TopCat.{0}} (x : X) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x

private theorem mapSigma_hom_ext {C D : Type*} [Category C] [Category D] {ι : Type*}
    (F : C ⥤ D) (S : ι → C) [HasCoproduct S]
    [PreservesColimit (Discrete.functor S) F]
    {B : D} {f g : F.obj (∐ S) ⟶ B}
    (h : ∀ i, F.map (Sigma.ι S i) ≫ f = F.map (Sigma.ι S i) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit F S) f g h

private theorem coproduct_stalk_hom_ext {X : TopCat.{0}} {P : Set X} (A : P → G) (x : X)
    {B : G} {f g : (stalkAt x).obj (pointCoproduct A) ⟶ B}
    (h : ∀ p : P, (stalkAt x).map (inclusion A p) ≫ f =
      (stalkAt x).map (inclusion A p) ≫ g) : f = g := by
  classical
  letI : PreservesColimitsOfSize.{0, 0} (stalkAt x) :=
    (stalkSkyscraperSheafAdjunction (C := G) x).leftAdjoint_preservesColimits
  exact mapSigma_hom_ext (stalkAt x) (part A) h

private theorem part_stalk_isZero {X : TopCat.{0}} {P : Set X} (A : P → G)
    (hClosed : ∀ p : P, IsClosed ({(p : X)} : Set X)) (p : P) {x : X} (h : x ≠ (p : X)) :
    IsZero ((stalkAt x).obj (part A p)) := by
  classical
  have hn : ¬ Specializes (p : X) x := by
    intro hsp
    exact h (Set.mem_singleton_iff.mp (hsp.mem_closed (hClosed p) (by simp)))
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal (p : X) (A p) hn).isZero

private theorem coproduct_stalk_isZero {X : TopCat.{0}} {P : Set X} (A : P → G)
    (hClosed : ∀ p : P, IsClosed ({(p : X)} : Set X)) {x : X} (h : x ∉ P) :
    IsZero ((stalkAt x).obj (pointCoproduct A)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply coproduct_stalk_hom_ext A x
  intro p
  have hz : IsZero ((stalkAt x).obj (part A p)) := by
    apply part_stalk_isZero A hClosed p
    intro e
    exact h (by simpa [e] using p.property)
  exact hz.eq_of_src _ _

private theorem stalkProjection_injective {X : TopCat.{0}} {P : Set X} (A : P → G)
    (hClosed : ∀ p : P, IsClosed ({(p : X)} : Set X)) (p : P) :
    Function.Injective ((stalkAt (p : X)).map (projection A p)) := by
  let F := stalkAt (p : X)
  have h : F.map (projection A p) ≫ F.map (inclusion A p) = 𝟙 _ := by
    apply coproduct_stalk_hom_ext A (p : X)
    intro q
    by_cases hqp : q = p
    · subst q
      change F.map (inclusion A p) ≫ (F.map (projection A p) ≫ F.map (inclusion A p)) =
        F.map (inclusion A p) ≫ 𝟙 _
      rw [← Category.assoc, ← F.map_comp, inclusion_projection_self, F.map_id,
        Category.id_comp, Category.comp_id]
    · apply (part_stalk_isZero A hClosed q (fun e => hqp (Subtype.ext e.symm))).eq_of_src
  have hl : Function.LeftInverse (F.map (inclusion A p)) (F.map (projection A p)) := by
    intro v
    change (F.map (projection A p) ≫ F.map (inclusion A p)) v = v
    rw [h, AddCommGrpCat.id_apply]
  exact hl.injective

private theorem eq_of_projections {X : TopCat.{0}} {P : Set X} (A : P → G)
    (hClosed : ∀ p : P, IsClosed ({(p : X)} : Set X)) (U : Opens X)
    (s t : (pointCoproduct A).obj.obj (op U))
    (h : ∀ p : P, (projection A p).hom.app (op U) s = (projection A p).hom.app (op U) t) :
    s = t := by
  refine TopCat.Presheaf.section_ext (show TopCat.Sheaf G X from pointCoproduct A) U s t fun x hx => ?_
  by_cases hxP : x ∈ P
  · let p : P := ⟨x, hxP⟩
    apply stalkProjection_injective A hClosed p
    change (TopCat.Presheaf.stalkFunctor G x).map (projection A p).hom
      (TopCat.Presheaf.germ (pointCoproduct A).obj U x hx s) =
        (TopCat.Presheaf.stalkFunctor G x).map (projection A p).hom
          (TopCat.Presheaf.germ (pointCoproduct A).obj U x hx t)
    simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply, h p] <;> rfl
  · letI : Subsingleton (TopCat.Presheaf.stalk (C := G) (pointCoproduct A).obj x) :=
      AddCommGrpCat.subsingleton_of_isZero (coproduct_stalk_isZero A hClosed hxP)
    exact Subsingleton.elim _ _

private theorem point_restrict_isIso {X : TopCat.{0}} (p : X) (A : G)
    {U V : Opens X} (i : U ⟶ V) (hp : p ∈ U) :
    IsIso ((pointSummand p A).obj.map i.op) := by
  classical
  change IsIso ((skyscraperPresheaf p A).map i.op)
  have hpV : p ∈ V := leOfHom i hp
  have hEq : (skyscraperPresheaf p A).obj (op V) = (skyscraperPresheaf p A).obj (op U) := by
    simp [skyscraperPresheaf_obj, hp, hpV]
  rw [skyscraperPresheaf_map, dif_pos hp]
  exact (eqToIso hEq).isIso_hom

private theorem closed_prime {P : Set X₀} (hP : (⊥ : PrimeSpectrum ℤ) ∉ P) (p : P) :
    IsClosed ({(p : X₀)} : Set X₀) := by
  refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal (p : X₀)).2
    (IsPrime.to_maximal_ideal ?_)
  intro h
  have hp : (p : X₀) = (⊥ : PrimeSpectrum ℤ) :=
    PrimeSpectrum.ext_iff.mpr (h.trans PrimeSpectrum.asIdeal_bot.symm)
  exact hP (hp ▸ p.property)

/-- Arbitrary sums of skyscrapers at nonzero primes of Spec ℤ are flasque. -/
theorem pointCoproduct_isFlasque {P : Set X₀} (A : P → G)
    (hP : (⊥ : PrimeSpectrum ℤ) ∉ P) :
    TopCat.Sheaf.IsFlasque (pointCoproduct A) := by
  classical
  constructor
  intro U V r
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro s
  let F := pointCoproduct A
  let η : X₀ := (⊥ : PrimeSpectrum ℤ)
  have hClosed := closed_prime hP
  by_cases hV : ((unop V : Opens X₀) : Set X₀).Nonempty
  · obtain ⟨x, hx⟩ := hV
    have hηV : η ∈ unop V :=
      ((PrimeSpectrum.le_iff_specializes η x).mp bot_le).mem_open (unop V).isOpen hx
    letI : Subsingleton (TopCat.Presheaf.stalk (C := G) F.obj η) :=
      AddCommGrpCat.subsingleton_of_isZero
        (coproduct_stalk_isZero A hClosed (x := η) hP)
    have hZero : TopCat.Presheaf.germ F.obj (unop V) η hηV s = TopCat.Presheaf.germ F.obj (unop V) η hηV 0 :=
      Subsingleton.elim _ _
    obtain ⟨W, hηW, i, _, hW⟩ := TopCat.Presheaf.germ_eq F.obj η hηV hηV s 0 hZero
    have hW0 : F.obj.map i.op s = 0 := hW.trans (map_zero _)
    have hFinite := GenericPointSupportDetection.specInt_generic_neighborhood_compl_finite W hηW
    let B : Set P := {p | (p : X₀) ∉ W}
    have hB : B.Finite := hFinite.preimage Subtype.val_injective.injOn
    let J := hB.toFinset
    have hLift (p : P) : ∃ a : (part A p).obj.obj U,
        (part A p).obj.map r a = (projection A p).hom.app V s := by
      letI := pointSummand_isFlasque (p : X₀) (A p)
      exact (AddCommGrpCat.epi_iff_surjective _).1 inferInstance _
    choose a ha using hLift
    let t : F.obj.obj U := ∑ p ∈ J, (inclusion A p).hom.app U (a p)
    refine ⟨t, eq_of_projections A hClosed (unop V) _ _ fun p => ?_⟩
    have hEach (q : P) :
        (projection A p).hom.app V (F.obj.map r ((inclusion A q).hom.app U (a q))) =
          if q = p then (projection A p).hom.app V s else 0 := by
      have hn := ConcreteCategory.congr_hom ((inclusion A q).hom.naturality r) (a q)
      change (inclusion A q).hom.app V ((part A q).obj.map r (a q)) =
        F.obj.map r ((inclusion A q).hom.app U (a q)) at hn
      rw [← hn]
      change ((inclusion A q ≫ projection A p).hom.app V) ((part A q).obj.map r (a q)) = _
      by_cases e : q = p
      · subst q
        rw [inclusion_projection_self, if_pos rfl]
        exact ha p
      · rw [inclusion_projection_ne A e, if_neg e] <;> rfl
    have hSum :
        (projection A p).hom.app V (F.obj.map r t) =
          ∑ q ∈ J, if q = p then (projection A p).hom.app V s else 0 := by
      simp only [t, map_sum, hEach]
    rw [hSum]
    by_cases hp : p ∈ J
    · rw [Finset.sum_eq_single p (fun q _ hq => if_neg hq) (fun h => (h hp).elim), if_pos rfl]
    · have hpW : (p : X₀) ∈ W := by
        by_contra h
        exact hp (by simpa [J, B] using h)
      have hProj : (part A p).obj.map i.op ((projection A p).hom.app V s) = 0 := by
        have hn := (ConcreteCategory.congr_hom ((projection A p).hom.naturality i.op) s).symm
        change (part A p).obj.map i.op ((projection A p).hom.app V s) =
          (projection A p).hom.app (op W) (F.obj.map i.op s) at hn
        simpa only [hW0, map_zero] using hn
      letI := point_restrict_isIso (p : X₀) (A p) i hpW
      have hz : (projection A p).hom.app V s = 0 := by
        apply (AddCommGrpCat.mono_iff_injective _).1
          (inferInstance : Mono ((part A p).obj.map i.op))
        simpa only [map_zero] using hProj
      simp [hz]
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact TopCat.Presheaf.section_ext (show TopCat.Sheaf G X₀ from F) (unop V) 0 s
      (fun x hx => (hV ⟨x, hx⟩).elim)

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

/-- The full native skyscraper direct sum in Paper 6 has zero first cohomology. -/
theorem pointCoproduct_H1_subsingleton {P : Set X₀} (A : P → G)
    (hP : (⊥ : PrimeSpectrum ℤ) ∉ P) :
    Subsingleton ((pointCoproduct A).H 1) := by
  letI := pointCoproduct_isFlasque A hP
  exact flasque_H1_subsingleton _

/-- The printed direct-sum comparison fails whenever an indexed coefficient is nonzero. -/
theorem paper6_direct_sum_comparison_refuted {P : Set X₀} (A : P → G)
    (hP : (⊥ : PrimeSpectrum ℤ) ∉ P) (p : P) (hp : Nontrivial (A p)) :
    ¬ Nonempty (((pointCoproduct A).H 1) ≃+ DirectSum P (fun q => (A q : Type))) := by
  classical
  rintro ⟨e⟩
  letI := pointCoproduct_H1_subsingleton A hP
  letI : Subsingleton (DirectSum P (fun q => (A q : Type))) := e.symm.injective.subsingleton
  have hinj : Function.Injective (DirectSum.of (fun q : P => (A q : Type)) p) :=
    DirectSum.of_injective p
  have hs : Subsingleton (A p) := hinj.subsingleton
  exact (not_nontrivial_iff_subsingleton.mpr hs) hp

end

end ManuscriptAudit.SpecIntSkyscraperSumHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntSkyscraperSumHOne.pointCoproduct_isFlasque,
      ``ManuscriptAudit.SpecIntSkyscraperSumHOne.pointCoproduct_H1_subsingleton,
      ``ManuscriptAudit.SpecIntSkyscraperSumHOne.paper6_direct_sum_comparison_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
