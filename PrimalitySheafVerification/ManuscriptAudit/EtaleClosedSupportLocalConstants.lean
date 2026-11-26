import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousDirectImageMaps

/-! Sections of the direct image of discrete-valued functions along a
closed immersion are locally constant along the closed support. -/

namespace ManuscriptAudit.EtaleClosedSupportLocalConstants

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleContinuousDirectImageMaps

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M]
variable [IsTopologicalAddGroup M]

def openObject (U : X.Etale) (W : U.left.Opens) : X.Etale := by
  letI : Etale U.hom := U.prop
  exact Scheme.Etale.mk (W.ι ≫ U.hom)

def openArrow (U : X.Etale) (W : U.left.Opens) : openObject U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl

private abbrev projection (U : X.Etale) := pullback.fst U.hom i

private theorem restricted_point_in_open (U : X.Etale) (W : U.left.Opens)
    (q : ((etaleBaseChange i).obj (openObject U W)).left) :
    projection i U (((etaleBaseChange i).map (openArrow U W)).left q) ∈ W := by
  have h : ((etaleBaseChange i).map (openArrow U W)).left ≫ projection i U =
      projection i (openObject U W) ≫ W.ι := by
    simp only [projection, etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst] <;> rfl
  have hq := congrArg (fun f => f q) h
  change projection i U (((etaleBaseChange i).map (openArrow U W)).left q) =
    W.ι (projection i (openObject U W) q) at hq
  rw [hq]
  exact (projection i (openObject U W) q).property

/-- Every point has an actual open neighborhood on whose conductor
pullback the section is constant. -/
theorem exists_open_restriction_const (U : X.Etale)
    (s : (functionsOver M i).obj.obj (op U)) (p : U.left) :
    ∃ W : U.left.Opens, p ∈ W ∧ ∃ a : M,
      (functionsOver M i).obj.map (openArrow U W).op s =
        ContinuousMap.const ((etaleBaseChange i).obj (openObject U W)).left a := by
  classical
  let f := projection i U
  have hf := f.isClosedEmbedding
  by_cases hp : p ∈ Set.range f
  · obtain ⟨z, hz⟩ := hp
    let a := s z
    let C : Set ((etaleBaseChange i).obj U).left := {x | s x ≠ a}
    have hC : IsClosed C := (isClosed_discrete ({a}ᶜ : Set M)).preimage s.continuous
    let W : U.left.Opens := ⟨(f '' C)ᶜ, (hf.isClosedMap _ hC).isOpen_compl⟩
    refine ⟨W, ?_, a, ?_⟩
    · rintro ⟨x, hx, he⟩
      change s x ≠ a at hx
      have h : x = z := hf.injective (he.trans hz.symm)
      exact hx (congrArg s h)
    · apply ContinuousMap.ext
      intro q
      let v := ((etaleBaseChange i).map (openArrow U W)).left q
      change s v = a
      by_contra h
      have hm : f v ∈ W := restricted_point_in_open i U W q
      exact hm ⟨v, h, rfl⟩
  · let W : U.left.Opens := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
    refine ⟨W, hp, 0, ?_⟩
    apply ContinuousMap.ext
    intro q
    let v := ((etaleBaseChange i).map (openArrow U W)).left q
    have hm : f v ∈ W := restricted_point_in_open i U W q
    exact (hm ⟨v, rfl⟩).elim

end
end ManuscriptAudit.EtaleClosedSupportLocalConstants

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleClosedSupportLocalConstants.exists_open_restriction_const
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
