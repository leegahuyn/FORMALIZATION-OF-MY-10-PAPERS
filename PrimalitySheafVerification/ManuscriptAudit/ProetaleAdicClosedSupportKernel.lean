import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicZeroSlice
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCounitMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! Native adic extension by zero along a quasi-compact open is the
closed restriction kernel. Over each affine chart a genuine weakly
étale affine zero slice supplies the required local lifting. -/

namespace ManuscriptAudit.ProetaleAdicClosedSupportKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K inc)
open ProetaleOpenCounitMono (rawCounit rawCounit_isIso_on_range
  extensionRestrictionMap extensionRestrictionMap_isIso)
open OpenProetaleExtension (extensionByZero)
open ProetaleClosedOpenRestriction (restrictionKernelIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev F := K i (M ℓ)
private abbrev J := Scheme.ProEt.topology X

private theorem kernel_value_zero (U : X.ProEt) (s : (F i ℓ).obj.obj (op U))
    (x : U.left) (hx : U.hom x ∈ Set.range i) :
    (show C(U.left, M ℓ) from ((inc i (M ℓ)).hom.app (op U) s).down) x = 0 := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := i) x z hz.symm
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : F i ℓ ⟶ functionsOver (M ℓ) i ↦ f.hom.app (op U))
      (kernel.condition (diagonal (M ℓ) i))) s
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback U.hom i : Scheme.{0}), M ℓ)) ↦ f.down p) h
  change (show C(U.left, M ℓ) from ((inc i (M ℓ)).hom.app (op U) s).down)
    (pullback.fst U.hom i p) = 0 at h'
  rwa [hp] at h'

set_option maxHeartbeats 3600000 in
private theorem affine_imageSieve_mem (hComplement : Set.range j = (Set.range i)ᶜ)
    (T : X.ProEt) [IsAffine T.left] (s : (F i ℓ).obj.obj (op T)) :
    Presheaf.imageSieve (rawCounit j (F i ℓ)) s ∈ J (X := X) T := by
  let f : C(T.left, M ℓ) := ((inc i (M ℓ)).hom.app (op T) s).down
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
    · have hi : T.hom x ∈ Set.range i := by
        by_contra h
        exact hx (hComplement.symm ▸ h)
      have hx₀ : x ∈ Set.range g := by
        rw [hg]
        exact kernel_value_zero i ℓ T s x hi
      obtain ⟨z, hz⟩ := hx₀
      exact ⟨false, z, hz⟩
  have hCover := ProetaleFiniteQuasiCompactCover.covering D a hQC hCov
  apply (J (X := X)).superset_covering _ hCover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨b⟩
  cases b
  · refine ⟨0, ?_⟩
    change (rawCounit j (F i ℓ)).app (op V₀) 0 = (F i ℓ).obj.map v.op s
    rw [map_zero]
    symm
    apply SheafSectionDifference.section_injective (inc i (M ℓ)) V₀
    rw [NatTrans.naturality_apply (inc i (M ℓ)).hom v.op s, map_zero]
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
    letI := rawCounit_isIso_on_range j (F i ℓ) W hW
    exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance ((F i ℓ).obj.map w.op s)

private theorem locallySurjective (hComplement : Set.range j = (Set.range i)ᶜ) :
    Presheaf.IsLocallySurjective (J (X := X)) (rawCounit j (F i ℓ)) where
  imageSieve_mem {T} s := by
    apply ProetaleFiniteQuasiCompactCover.of_affine_pullbacks
    intro V _ a
    rw [Presheaf.pullback_imageSieve]
    exact affine_imageSieve_mem i j ℓ hComplement V ((F i ℓ).obj.map a.op s)

/-- The outgoing actual closed restriction kernel is extension by zero from
the complementary quasi-compact open, for genuine continuous adic coefficients. -/
def extensionKernelIso (hComplement : Set.range j = (Set.range i)ᶜ) :
    (extensionByZero j A).obj (functions (M ℓ) Y) ≅ F i ℓ := by
  letI := extensionRestrictionMap_isIso j (F i ℓ) (locallySurjective i j ℓ hComplement)
  exact ((extensionByZero j A).mapIso (restrictionKernelIso i j (M ℓ) hComplement)).symm ≪≫
    asIso (extensionRestrictionMap j (F i ℓ))

end

end ManuscriptAudit.ProetaleAdicClosedSupportKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicClosedSupportKernel.extensionKernelIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
