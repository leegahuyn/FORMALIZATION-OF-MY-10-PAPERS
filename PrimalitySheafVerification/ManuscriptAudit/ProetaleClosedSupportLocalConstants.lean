import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! Any discrete-valued section on an actual closed support is
locally constant on ordinary neighborhoods in the native pro-étale site. -/

namespace ManuscriptAudit.ProetaleClosedSupportLocalConstants

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange)
open ProetaleContinuousDirectImageMaps (functionsOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M]

abbrev openObject (U : X.ProEt) (W : U.left.Opens) : X.ProEt :=
  Scheme.ProEt.mk (W.ι ≫ U.hom)

abbrev openArrow (U : X.ProEt) (W : U.left.Opens) : openObject U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl

private abbrev projection (U : X.ProEt) := pullback.fst U.hom i

private theorem restricted_point_in_open (U : X.ProEt) (W : U.left.Opens)
    (q : ((baseChange i).obj (openObject U W)).left) :
    projection i U (((baseChange i).map (openArrow U W)).left q) ∈ W := by
  have h : ((baseChange i).map (openArrow U W)).left ≫ projection i U =
      projection i (openObject U W) ≫ W.ι := by
    simp only [projection, baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst] <;> rfl
  have hq := congrArg (fun f ↦ f q) h
  change projection i U (((baseChange i).map (openArrow U W)).left q) =
    W.ι (projection i (openObject U W) q) at hq
  rw [hq]
  exact (projection i (openObject U W) q).property

/-- Every chart point has an ordinary open neighborhood on whose closed
pullback the given native section is constant. -/
theorem exists_open_restriction_const (U : X.ProEt)
    (s : (functionsOver M i).obj.obj (op U)) (p : U.left) :
    ∃ W : U.left.Opens, p ∈ W ∧ ∃ a : M,
      (functionsOver M i).obj.map (openArrow U W).op s =
        ⟨ContinuousMap.const ((baseChange i).obj (openObject U W)).left a⟩ := by
  classical
  let s' : C(((baseChange i).obj U).left, M) := s.down
  let f := projection i U
  have hf := f.isClosedEmbedding
  by_cases hp : p ∈ Set.range f
  · obtain ⟨z, hz⟩ := hp
    let a := s' z
    let C₀ : Set ((baseChange i).obj U).left := {x | s' x ≠ a}
    have hC : IsClosed C₀ := (isClosed_discrete ({a}ᶜ : Set M)).preimage s'.continuous
    let W : U.left.Opens := ⟨(f '' C₀)ᶜ, (hf.isClosedMap _ hC).isOpen_compl⟩
    refine ⟨W, ?_, a, ?_⟩
    · rintro ⟨x, hx, he⟩
      change s' x ≠ a at hx
      exact hx (congrArg s' (hf.injective (he.trans hz.symm)))
    · apply ULift.ext
      apply ContinuousMap.ext
      intro q
      let v := ((baseChange i).map (openArrow U W)).left q
      change s' v = a
      by_contra h
      have hm : f v ∈ W := restricted_point_in_open i U W q
      exact hm ⟨v, h, rfl⟩
  · let W : U.left.Opens := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
    refine ⟨W, hp, 0, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro q
    let v := ((baseChange i).map (openArrow U W)).left q
    have hm : f v ∈ W := restricted_point_in_open i U W q
    exact (hm ⟨v, rfl⟩).elim

end
end ManuscriptAudit.ProetaleClosedSupportLocalConstants

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleClosedSupportLocalConstants.exists_open_restriction_const
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
