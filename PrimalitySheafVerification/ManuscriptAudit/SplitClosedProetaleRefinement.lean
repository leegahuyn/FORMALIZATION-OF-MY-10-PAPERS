import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedEtaleRefinement
import PrimalitySheafVerification.ManuscriptAudit.AffineFlatClosedGraphLift

/-! Affine weakly étale neighborhoods of a split closed fiber extend
to affine weakly étale neighborhoods of the ambient scheme. -/

namespace ManuscriptAudit.SplitClosedProetaleRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SplitClosedEtaleRefinement

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S T U W : Scheme.{u}} [IsAffine S] [IsAffine U] [IsAffine W]
variable (a : U ⟶ T) (i : S ⟶ T) (r : T ⟶ S)
variable (w : W ⟶ pullback a i)
variable [IsClosedImmersion i] [WeaklyEtale a] [WeaklyEtale w]

/-- A chart on the actual closed fiber is an actual pullback after refining
the split ambient weakly étale chart by localization. -/
theorem exists_refinement (hir : i ≫ r = 𝟙 S) :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (v : V ⟶ U) (_ : WeaklyEtale v) (t : W ⟶ V),
      IsPullback t (wToBase a i w) (v ≫ a) i ∧
      t ≫ v = w ≫ pullback.fst a i := by
  let p := pullback.snd (wToBase a i w) (a ≫ r)
  let m := fiberInAmbient a i r w hir
  have hm : IsPullback m (pullback.snd _ _) p (pullback.fst a i) :=
    fiberInAmbient_isPullback a i r w hir
  letI : IsClosedImmersion m := MorphismProperty.of_isPullback hm.flip
    (inferInstanceAs (IsClosedImmersion (pullback.fst a i)))
  let g := graph a i w
  letI : IsAffine (pullback a i) := isAffine_of_isAffineHom (pullback.fst a i)
  letI : IsSeparated (fiberToBase a i) := IsSeparated.of_isAffineHom _
  have hg := pullback_lift_diagonal_isPullback w (fiberToBase a i)
  letI : IsClosedImmersion g := MorphismProperty.of_isPullback
    (P := @IsClosedImmersion) hg inferInstance
  letI : Flat g := MorphismProperty.of_isPullback (P := @Flat) hg inferInstance
  letI : IsAffine (ambient a i r w) := by
    change IsAffine (pullback (wToBase a i w) (a ≫ r))
    infer_instance
  obtain ⟨V, hV, j, hj, t, h⟩ := AffineFlatClosedGraphLift.exists_weaklyEtale_pullback m g
  letI : WeaklyEtale j := hj
  letI : WeaklyEtale (wToBase a i w) := by
    dsimp only [wToBase, fiberToBase]
    infer_instance
  have hcomp := h.paste_vert hm
  have hgs : g ≫ pullback.snd (wToBase a i w) (fiberToBase a i) = w := by
    simp only [g, graph, pullback.lift_snd]
  have hFinal := hcomp.paste_vert (IsPullback.of_hasPullback a i)
  refine ⟨V, hV, j ≫ p, inferInstance, t, ?_, ?_⟩
  · rw [hgs] at hFinal
    exact hFinal
  · simpa only [hgs] using hcomp.w

end
end ManuscriptAudit.SplitClosedProetaleRefinement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SplitClosedProetaleRefinement.exists_refinement
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
