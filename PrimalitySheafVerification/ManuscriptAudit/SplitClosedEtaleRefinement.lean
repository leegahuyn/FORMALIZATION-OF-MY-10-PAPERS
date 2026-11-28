import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Étale neighborhoods over a split closed immersion extend after an ambient open restriction. -/

namespace ManuscriptAudit.SplitClosedEtaleRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S T U W : Scheme.{u}}
variable (a : U ⟶ T) (i : S ⟶ T) (r : T ⟶ S)
variable (w : W ⟶ pullback a i)

abbrev fiberToBase := pullback.snd a i
abbrev wToBase := w ≫ fiberToBase a i

abbrev ambient := pullback (wToBase a i w) (a ≫ r)
abbrev fiberProduct := pullback (wToBase a i w) (fiberToBase a i)

private theorem fiber_agrees (hir : i ≫ r = 𝟙 S) :
    pullback.fst a i ≫ a ≫ r = fiberToBase a i := by
  rw [pullback.condition_assoc, hir, Category.comp_id]

def fiberInAmbient (hir : i ≫ r = 𝟙 S) :
    fiberProduct a i w ⟶ ambient a i r w :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst a i) (by
    rw [Category.assoc, fiber_agrees a i r hir]
    exact pullback.condition)

theorem fiberInAmbient_isPullback (hir : i ≫ r = 𝟙 S) :
    IsPullback (fiberInAmbient a i r w hir) (pullback.snd _ _)
      (pullback.snd (wToBase a i w) (a ≫ r)) (pullback.fst a i) := by
  have h : IsPullback (fiberInAmbient a i r w hir ≫ pullback.fst _ _) (pullback.snd _ _)
      (wToBase a i w) (pullback.fst a i ≫ (a ≫ r)) := by
    rw [fiber_agrees a i r hir]
    simpa only [fiberInAmbient, pullback.lift_fst] using
      (IsPullback.of_hasPullback (wToBase a i w) (fiberToBase a i))
  exact h.of_right (by simp only [fiberInAmbient, pullback.lift_snd])
    (IsPullback.of_hasPullback (wToBase a i w) (a ≫ r))

def graph : W ⟶ fiberProduct a i w :=
  pullback.lift (𝟙 W) w (Category.id_comp _)

private theorem graph_open [Etale a] : IsOpenImmersion (graph a i w) := by
  change IsOpenImmersion (pullback.lift (𝟙 W) w (Category.id_comp _))
  exact MorphismProperty.of_isPullback
    (pullback_lift_diagonal_isPullback w (fiberToBase a i))
    (inferInstanceAs (IsOpenImmersion (pullback.diagonal (fiberToBase a i))))

private theorem extend_open {P Q : Scheme.{u}} (m : P ⟶ Q) [IsClosedImmersion m]
    (R : P.Opens) : ∃ O : Q.Opens, m ⁻¹ᵁ O = R := by
  obtain ⟨O, hO, he⟩ := m.isClosedEmbedding.isInducing.isOpen_iff.mp R.2
  exact ⟨⟨O, hO⟩, TopologicalSpace.Opens.ext he⟩

/-- A native étale chart above the fiber of a split closed immersion is a pullback of an
étale chart above the ambient scheme, with its given projection to the original fiber. -/
theorem exists_refinement [IsClosedImmersion i] [Etale a] [Etale w]
    (hir : i ≫ r = 𝟙 S) :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : Etale v) (t : W ⟶ V),
      IsPullback t (wToBase a i w) (v ≫ a) i ∧
      t ≫ v = w ≫ pullback.fst a i := by
  let m := fiberInAmbient a i r w hir
  let p := pullback.snd (wToBase a i w) (a ≫ r)
  have hm : IsPullback m (pullback.snd _ _) p (pullback.fst a i) :=
    fiberInAmbient_isPullback a i r w hir
  letI : IsClosedImmersion m := MorphismProperty.of_isPullback hm.flip
    (inferInstanceAs (IsClosedImmersion (pullback.fst a i)))
  let g := graph a i w
  letI : IsOpenImmersion g := graph_open a i w
  obtain ⟨O, hO⟩ := extend_open m g.opensRange
  let e : W ≅ (m ⁻¹ᵁ O : (fiberProduct a i w).Opens) :=
    g.isoOpensRange ≪≫ (fiberProduct a i w).isoOfEq hO.symm
  have he : e.hom ≫ (m ⁻¹ᵁ O).ι = g := by simp [e]
  let t := e.hom ≫ (m ∣_ O)
  have hg : IsPullback t g O.ι m := by
    refine (isPullback_morphismRestrict m O).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp only [t, Iso.refl_hom, Category.comp_id]
    · simpa only [Iso.refl_hom, Category.comp_id] using he
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  have hcomp := hg.paste_vert hm
  have hgs : g ≫ pullback.snd (wToBase a i w) (fiberToBase a i) = w := by
    simp only [g, graph, pullback.lift_snd]
  have hFinal := hcomp.paste_vert (IsPullback.of_hasPullback a i)
  refine ⟨O, O.ι ≫ p, ?_, t, ?_, ?_⟩
  · letI : Etale (wToBase a i w) := by dsimp [wToBase, fiberToBase]; infer_instance
    exact inferInstanceAs (Etale (O.ι ≫ pullback.snd (wToBase a i w) (a ≫ r)))
  · rw [hgs] at hFinal
    exact hFinal
  · simpa only [hgs] using hcomp.w

end

end ManuscriptAudit.SplitClosedEtaleRefinement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SplitClosedEtaleRefinement.exists_refinement
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
