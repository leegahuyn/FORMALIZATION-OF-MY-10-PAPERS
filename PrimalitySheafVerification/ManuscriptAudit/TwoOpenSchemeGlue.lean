import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Two schemes covered by the same two open charts are isomorphic
when the ordinary scheme pullbacks agree with their projection maps. -/

namespace ManuscriptAudit.TwoOpenSchemeGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {U V X Y : Scheme.{u}}

private def pairObjects (U V : Scheme.{u}) : Bool → Scheme.{u}
  | false => U
  | true => V

private def pairArrows (j : U ⟶ X) (k : V ⟶ X) :
    ∀ i : Bool, pairObjects U V i ⟶ X
  | false => j
  | true => k

private def pairCover (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (h : Set.range j ∪ Set.range k = Set.univ) : X.OpenCover where
  I₀ := Bool
  X := pairObjects U V
  f := pairArrows j k
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      have hx : x ∈ Set.range j ∪ Set.range k := h.symm ▸ Set.mem_univ x
      rcases hx with hj | hk
      · exact ⟨false, hj⟩
      · exact ⟨true, hk⟩
    · intro b
      cases b
      · exact inferInstanceAs (IsOpenImmersion j)
      · exact inferInstanceAs (IsOpenImmersion k)

private theorem pairCompat (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (a : U ⟶ Y) (b : V ⟶ Y)
    (h : pullback.fst j k ≫ a = pullback.snd j k ≫ b) :
    ∀ i l : Bool, pullback.fst (pairArrows j k i) (pairArrows j k l) ≫ pairArrows a b i =
      pullback.snd (pairArrows j k i) (pairArrows j k l) ≫ pairArrows a b l := by
  intro i l
  cases i <;> cases l
  · change pullback.fst j j ≫ a = pullback.snd j j ≫ a
    exact congrArg (fun f => f ≫ a) ((cancel_mono j).mp (pullback.condition (f := j) (g := j)))
  · exact h
  · change pullback.fst k j ≫ b = pullback.snd k j ≫ a
    calc
      _ = (pullbackSymmetry k j).hom ≫ (pullback.snd j k ≫ b) := by
        rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]
      _ = (pullbackSymmetry k j).hom ≫ (pullback.fst j k ≫ a) := by rw [h]
      _ = _ := by rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  · change pullback.fst k k ≫ b = pullback.snd k k ≫ b
    exact congrArg (fun f => f ≫ b) ((cancel_mono k).mp (pullback.condition (f := k) (g := k)))

variable (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
variable (a : U ⟶ Y) (b : V ⟶ Y)
variable (hX : Set.range j ∪ Set.range k = Set.univ)

private def glueTwo (h : pullback.fst j k ≫ a = pullback.snd j k ≫ b) : X ⟶ Y :=
  (pairCover j k hX).glueMorphisms (pairArrows a b) (pairCompat j k a b h)

private theorem glueTwo_left (h : pullback.fst j k ≫ a = pullback.snd j k ≫ b) :
    j ≫ glueTwo j k a b hX h = a :=
  (pairCover j k hX).ι_glueMorphisms _ _ false

private theorem glueTwo_right (h : pullback.fst j k ≫ a = pullback.snd j k ≫ b) :
    k ≫ glueTwo j k a b hX h = b :=
  (pairCover j k hX).ι_glueMorphisms _ _ true

private theorem compatible_of_overlapIso
    (e : pullback j k ≅ pullback a b)
    (hf : e.hom ≫ pullback.fst a b = pullback.fst j k)
    (hs : e.hom ≫ pullback.snd a b = pullback.snd j k) :
    pullback.fst j k ≫ a = pullback.snd j k ≫ b := by
  rw [← hf, ← hs, Category.assoc, Category.assoc, pullback.condition]

variable [IsOpenImmersion a] [IsOpenImmersion b]
variable (hY : Set.range a ∪ Set.range b = Set.univ)

/-- Glue the identity on each chart in both directions using the given
native intersection isomorphism and its actual projection equations. -/
def isoOfIntersections
    (e : pullback j k ≅ pullback a b)
    (hf : e.hom ≫ pullback.fst a b = pullback.fst j k)
    (hs : e.hom ≫ pullback.snd a b = pullback.snd j k) : X ≅ Y := by
  have h₁ := compatible_of_overlapIso j k a b e hf hs
  have hf' : e.inv ≫ pullback.fst j k = pullback.fst a b := by
    rw [← hf, Iso.inv_hom_id_assoc]
  have hs' : e.inv ≫ pullback.snd j k = pullback.snd a b := by
    rw [← hs, Iso.inv_hom_id_assoc]
  have h₂ := compatible_of_overlapIso a b j k e.symm hf' hs'
  let f := glueTwo j k a b hX h₁
  let g := glueTwo a b j k hY h₂
  refine ⟨f, g, ?_, ?_⟩
  · apply (pairCover j k hX).hom_ext
    intro i
    cases i
    · change j ≫ (f ≫ g) = j ≫ 𝟙 X
      rw [← Category.assoc, Category.comp_id]
      exact (congrArg (fun r => r ≫ g) (glueTwo_left j k a b hX h₁)).trans
        (glueTwo_left a b j k hY h₂)
    · change k ≫ (f ≫ g) = k ≫ 𝟙 X
      rw [← Category.assoc, Category.comp_id]
      exact (congrArg (fun r => r ≫ g) (glueTwo_right j k a b hX h₁)).trans
        (glueTwo_right a b j k hY h₂)
  · apply (pairCover a b hY).hom_ext
    intro i
    cases i
    · change a ≫ (g ≫ f) = a ≫ 𝟙 Y
      rw [← Category.assoc, Category.comp_id]
      exact (congrArg (fun r => r ≫ f) (glueTwo_left a b j k hY h₂)).trans
        (glueTwo_left j k a b hX h₁)
    · change b ≫ (g ≫ f) = b ≫ 𝟙 Y
      rw [← Category.assoc, Category.comp_id]
      exact (congrArg (fun r => r ≫ f) (glueTwo_right a b j k hY h₂)).trans
        (glueTwo_right j k a b hX h₁)

end
end ManuscriptAudit.TwoOpenSchemeGlue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoOpenSchemeGlue.isoOfIntersections
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
