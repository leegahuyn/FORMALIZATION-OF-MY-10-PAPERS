import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicZeroSlice
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCounitMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! A subsheaf of continuous adic functions whose sections vanish pointwise
outside a quasi-compact open is the native extension of its restriction. -/

namespace ManuscriptAudit.ProetaleAdicOpenSupportCriterion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleOpenCounitMono (rawCounit rawCounit_isIso_on_range
  extensionRestrictionMap extensionRestrictionMap_isIso)
open OpenProetaleExtension (extensionByZero restriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}}
variable (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev J := Scheme.ProEt.topology X

variable {F : Sheaf (J (X := X)) A} (inc : F ⟶ functions (M ℓ) X) [Mono inc]

/-- Each section vanishes pointwise wherever the chart leaves the open. -/
def VanishesOutside : Prop :=
  ∀ (T : X.ProEt) (s : F.obj.obj (op T)) (x : T.left), T.hom x ∉ Set.range j →
    (show C(T.left, M ℓ) from (inc.hom.app (op T) s).down) x = 0

set_option maxHeartbeats 3600000 in
private theorem affine_imageSieve_mem (hVan : VanishesOutside j ℓ inc)
    (T : X.ProEt) [IsAffine T.left] (s : F.obj.obj (op T)) :
    Presheaf.imageSieve (rawCounit j F) s ∈ J (X := X) T := by
  let f : C(T.left, M ℓ) := (inc.hom.app (op T) s).down
  obtain ⟨V, g, hAffine, hWeak, hg⟩ := ProetalePadicZeroSlice.exists_affine_chart ℓ f
  letI : IsAffine V := hAffine
  letI : WeaklyEtale g := hWeak
  letI : WeaklyEtale T.hom := T.prop
  let W : X.ProEt := Scheme.ProEt.mk (pullback.fst T.hom j ≫ T.hom)
  let V₀ : X.ProEt := Scheme.ProEt.mk (g ≫ T.hom)
  let v : V₀ ⟶ T := MorphismProperty.Over.homMk g rfl
  let w : W ⟶ T := MorphismProperty.Over.homMk (pullback.fst T.hom j) rfl
  let D : Bool → X.ProEt
    | false => V₀
    | true => W
  let a : ∀ b, D b ⟶ T
    | false => v
    | true => w
  have hQC (b : Bool) : QuasiCompact (a b).left := by
    cases b
    · exact inferInstanceAs (QuasiCompact g)
    · exact inferInstanceAs (QuasiCompact (pullback.fst T.hom j))
  have hCov (x : T.left) : ∃ b, ∃ y : (D b).left, (a b).left y = x := by
    by_cases hx : T.hom x ∈ Set.range j
    · obtain ⟨z, hz⟩ := hx
      obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := j) x z hz.symm
      exact ⟨true, p, hp⟩
    · have hx₀ : x ∈ Set.range g := by
        rw [hg]
        exact hVan T s x hx
      obtain ⟨z, hz⟩ := hx₀
      exact ⟨false, z, hz⟩
  have hCover := ProetaleFiniteQuasiCompactCover.covering D a hQC hCov
  apply (J (X := X)).superset_covering _ hCover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨b⟩
  cases b
  · refine ⟨0, ?_⟩
    change (rawCounit j F).app (op V₀) 0 = F.obj.map v.op s
    rw [map_zero]
    symm
    apply SheafSectionDifference.section_injective inc V₀
    rw [NatTrans.naturality_apply inc.hom v.op s, map_zero]
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change f (g y) = 0
    have hy : g y ∈ Set.range g := ⟨y, rfl⟩
    rwa [hg] at hy
  · have hW : Set.range W.hom ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      refine ⟨pullback.snd T.hom j y, ?_⟩
      exact (congrArg (fun u : pullback T.hom j ⟶ X ↦ u y)
        (pullback.condition (f := T.hom) (g := j))).symm
    letI := rawCounit_isIso_on_range j F W hW
    exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance (F.obj.map w.op s)

private theorem locallySurjective (hVan : VanishesOutside j ℓ inc) :
    Presheaf.IsLocallySurjective (J (X := X)) (rawCounit j F) where
  imageSieve_mem {T} s := by
    apply ProetaleFiniteQuasiCompactCover.of_affine_pullbacks
    intro V _ a
    rw [Presheaf.pullback_imageSieve]
    exact affine_imageSieve_mem j ℓ inc hVan V (F.obj.map a.op s)

/-- The actual extension by zero of the restricted subsheaf is the given subsheaf. -/
def extensionIso (hVan : VanishesOutside j ℓ inc) :
    (extensionByZero j A).obj ((restriction j A).obj F) ≅ F :=
  letI := extensionRestrictionMap_isIso j F (locallySurjective j ℓ inc hVan)
  asIso (extensionRestrictionMap j F)

end

end ManuscriptAudit.ProetaleAdicOpenSupportCriterion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicOpenSupportCriterion.extensionIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
