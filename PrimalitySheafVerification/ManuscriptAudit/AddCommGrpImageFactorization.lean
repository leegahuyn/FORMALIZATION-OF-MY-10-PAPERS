import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.CategoryTheory.MorphismProperty.Concrete

/-!
# Functorial surjection and injection for abelian groups

The ordinary categorical image gives the surjective-then-injective
factorization needed to identify epimorphisms of abelian sheaves with
locally surjective morphisms.
-/

namespace ManuscriptAudit.AddCommGrpImageFactorization

open CategoryTheory CategoryTheory.Limits

universe u

private noncomputable def imageFunctor : Arrow AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj f := image f.hom
  map f := image.map f
  map_id f := image.map_id f
  map_comp f g := image.map_comp f g

/-- Factorization through the categorical image is functorial and pointwise
surjective followed by injective. -/
theorem functorialSurjectiveInjectiveFactorization :
    ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat.{u} := by
  refine ⟨⟨{
    Z := imageFunctor
    i := {
      app f := factorThruImage f.hom
      naturality _ _ h := (image.factor_map h).symm }
    p := {
      app f := image.ι f.hom
      naturality _ _ h := image.map_ι h }
    fac := ?_
    hi := fun f => (AddCommGrpCat.epi_iff_surjective (factorThruImage f.hom)).mp inferInstance
    hp := fun f => (AddCommGrpCat.mono_iff_injective (image.ι f.hom)).mp inferInstance
  }⟩⟩
  ext1 f
  exact image.fac f.hom

end ManuscriptAudit.AddCommGrpImageFactorization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AddCommGrpImageFactorization.functorialSurjectiveInjectiveFactorization
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
