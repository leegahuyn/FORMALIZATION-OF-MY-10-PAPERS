import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCechSiteArrowDiagram
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineCechRawComparison
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineUnderRingRawEqualities
import PrimalitySheafVerification.ManuscriptAudit.NativeCechArrowFunctor
import PrimalitySheafVerification.ManuscriptAudit.NativeCechExactnessByAffineStages

/-! Native inverse-image Čech exactness passes through actual filtered
affine arrow colimits, in all positive degrees. -/

namespace ManuscriptAudit.NativeAffineCechArrowContinuity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NativeAffineCechRawComparison
  (nativePresheaf nativeArrow nerve comparison comparison_bijective comparison_natural)
open NativeAffineUnderRingRawSections (groups restriction)
open NativeCechNerve (Cech)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})
  (hComp : ∀ V : (X (A := A)).ProEt, IsAffine V.left →
    Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X (A := A)) I).app (op V)))

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  [HasColimitsOfShape J (Under (R (A := A)))]
  {F : J ⥤ Arrow (Under (R (A := A)))} (c : Cocone F)
  (hL : ∀ j, WeaklyEtale (Spec.map (F.obj j).left.hom))
  (hR : ∀ j, WeaklyEtale (Spec.map (F.obj j).right.hom))
  [WeaklyEtale (Spec.map c.pt.left.hom)] [WeaklyEtale (Spec.map c.pt.right.hom)]

local instance (j : J) : WeaklyEtale (Spec.map (F.obj j).left.hom) := hL j
local instance (j : J) : WeaklyEtale (Spec.map (F.obj j).right.hom) := hR j

private abbrev model (n : ℕ) := (AffineCechConerveFilteredColimit.degree n).mapCocone c

private abbrev actualCocone :=
  (NativeCechArrowFunctor.cochains (nativePresheaf I)).mapCocone
    (AffineCechSiteArrowDiagram.cocone @WeaklyEtale F hL hR c inferInstance inferInstance)

set_option maxHeartbeats 6000000 in
private theorem exists_affine_representative (hc : IsColimit c) (n : ℕ)
    (z : (nativePresheaf I).obj (op (nerve c.pt n))) :
    ∃ (i : J) (y : (nativePresheaf I).obj (op (nerve (F.obj i) n))),
      ((actualCocone I c hL hR).ι.app i).f n y = z := by
  obtain ⟨x, hx⟩ := (comparison_bijective I c.pt hComp n).surjective z
  let d := model c n
  obtain ⟨i, y, hy⟩ := NativeAffineUnderRingRawSections.exists_section I
    (fun i ↦ inferInstanceAs (WeaklyEtale (Spec.map (AffineCechConerveSpecLimit.degree (F.obj i) n).hom)))
    d (AffineCechConerveFilteredColimit.isColimit_degree hc n) x
  refine ⟨i, comparison I (F.obj i) n y, ?_⟩
  have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (comparison_natural I (c.ι.app i) n)) y
  change ((actualCocone I c hL hR).ι.app i).f n (comparison I (F.obj i) n y) =
    comparison I c.pt n (restriction I (d.ι.app i) y) at h
  exact h.trans ((congrArg (comparison I c.pt n) hy).trans hx)

set_option maxHeartbeats 6000000 in
private theorem detects_affine_zero (hc : IsColimit c) (n : ℕ) (i : J)
    (z : (nativePresheaf I).obj (op (nerve (F.obj i) n)))
    (hz : ((actualCocone I c hL hR).ι.app i).f n z = 0) :
    ∃ (j : J) (ij : i ⟶ j), ((actualCocone I c hL hR).ι.app  i).f n z = 0 ∧
      ((AffineCechSiteArrowDiagram.diagram @WeaklyEtale F hL hR ⋙
        NativeCechArrowFunctor.cochains (nativePresheaf I)).map ij).f n z = 0 := by
  obtain ⟨x, hx⟩ := (comparison_bijective I (F.obj i) hComp n).surjective z
  let d := model c n
  have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (comparison_natural I (c.ι.app i) n)) x
  change ((actualCocone I c hL hR).ι.app i).f n (comparison I (F.obj i) n x) =
    comparison I c.pt n (restriction I (d.ι.app i) x) at h
  rw [hx, hz] at h
  have h₀ : restriction I (d.ι.app i) x = restriction I (d.ι.app i) 0 := by
    rw [map_zero]
    apply (comparison_bijective I c.pt hComp n).injective
    rw [map_zero]
    exact h.symm
  obtain ⟨j, ij, hEq⟩ := NativeAffineUnderRingRawEqualities.exists_equal_stage I
    (fun i ↦ inferInstanceAs (WeaklyEtale (Spec.map (AffineCechConerveSpecLimit.degree (F.obj i) n).hom)))
    (AffineCechConerveFilteredColimit.isColimit_degree hc n) i x 0 h₀
  refine ⟨j, ij, hz, ?_⟩
  have h' := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (comparison_natural I (F.map ij) n)) x
  rw [map_zero] at hEq
  change ((AffineCechSiteArrowDiagram.diagram @WeaklyEtale F hL hR ⋙
    NativeCechArrowFunctor.cochains (nativePresheaf I)).map ij).f n
      (comparison I (F.obj i) n x) =
    comparison I (F.obj j) n (restriction I ((F ⋙ AffineCechConerveFilteredColimit.degree n).map ij) x) at h'
  rw [hx, hEq, map_zero] at h'
  exact h'

set_option maxHeartbeats 3900000 in
/-- The actual native tensor nerve is exact at the desired positive
degree if its actual filtered affine stage nerves are exact there. -/
theorem exactAt_succ (hc : IsColimit c) (n : ℕ)
    (hStage : ∀ j, (Cech (nativeArrow (F.obj j)) (nativePresheaf I)).ExactAt (n + 1)) :
    (Cech (nativeArrow c.pt) (nativePresheaf I)).ExactAt (n + 1) := by
  apply NativeCechExactnessByAffineStages.exactAt_succ (actualCocone I c hL hR) n
  · exact exists_affine_representative I hComp c hL hR hc (n + 1)
  · intro i z hz
    obtain ⟨j, ij, _, he⟩ := detects_affine_zero I hComp c hL hR hc (n + 2) i z hz
    exact ⟨j, ij, he⟩
  · exact hStage

end
end ManuscriptAudit.NativeAffineCechArrowContinuity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineCechArrowContinuity.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
