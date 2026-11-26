import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local lifts and epimorphisms of affine étale sheaves

A section on an affine étale object is locally lifted if each
underlying point is in the image of one diagram giving a lift.
Cover-density reduces this condition to chart objects.
-/

namespace ManuscriptAudit.AffineEtaleLocalSurjectivity

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

variable {C D : Type*} [Category* C] [Category* D] (J : GrothendieckTopology C)
variable {F G : Cᵒᵖ ⥤ AddCommGrpCat.{0}} (m : F ⟶ G)

/-- Local lifting on the objects of a cover-dense functor is enough. -/
theorem of_coverDense (i : D ⥤ C) [i.IsCoverDense J]
    (h : ∀ (U : D) (s : G.obj (op (i.obj U))), Presheaf.imageSieve m s ∈ J (i.obj U)) :
    Presheaf.IsLocallySurjective J m where
  imageSieve_mem {U} s := by
    apply J.transitive (i.is_cover_of_isCoverDense J U)
    intro V f hf
    obtain ⟨⟨W, a, b, rfl⟩⟩ := hf
    rw [← Sieve.pullback_comp, Presheaf.pullback_imageSieve]
    exact J.pullback_stable a (h W (G.map b.op s))

universe u

variable {X : Scheme.{u}}
variable {F' G' : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{0}} (m' : F' ⟶ G')

/-- The image sieve of a section is covering if every underlying point
lies in the image of an actual affine chart arrow with a local lift. -/
theorem imageSieve_mem_of_pointwise {U : X.AffineEtale} (s : G'.obj (op U))
    (h : ∀ x : ((Scheme.AffineEtale.Spec X).obj U).left,
      ∃ (V : X.AffineEtale) (f : V ⟶ U), Presheaf.imageSieve m' s f ∧
        x ∈ Set.range ((Scheme.AffineEtale.Spec X).map f).left) :
    Presheaf.imageSieve m' s ∈ Scheme.AffineEtale.topology X U := by
  classical
  choose V f hf hr using h
  have hCover : Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology X U := by
    let E := Scheme.AffineEtale.Spec X
    apply (E.functorPushforward_mem_iff (Scheme.AffineEtale.topology X) X.smallEtaleTopology).mp
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_iff_forall.mpr (fun x ↦ Set.mem_iUnion.mpr ⟨x, hr x⟩)
  apply (Scheme.AffineEtale.topology X).superset_covering _ hCover
  change Sieve.generate (Presieve.ofArrows V f) ≤ _
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact hf

end

end ManuscriptAudit.AffineEtaleLocalSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleLocalSurjectivity.of_coverDense,
      ``ManuscriptAudit.AffineEtaleLocalSurjectivity.imageSieve_mem_of_pointwise] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
