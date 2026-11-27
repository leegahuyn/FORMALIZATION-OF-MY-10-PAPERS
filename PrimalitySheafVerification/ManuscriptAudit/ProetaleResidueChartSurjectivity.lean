import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueSheaves
import PrimalitySheafVerification.ManuscriptAudit.SequentialInverseLimitDifference

/-! Every actual finite residue reduction is onto on every pro-étale chart. -/

namespace ManuscriptAudit.ProetaleResidueChartSurjectivity

open AlgebraicGeometry CategoryTheory Opposite
open PadicResidueSystems (reduction)
open ProetaleResidueSheaves (residueSheaf residueTransition)
open ProetalePadicSectionTower (sectionTransition)
open SequentialInverseLimitDifference (productDifference productDifference_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A section of a finite discrete residue level always lifts continuously to the next level. -/
theorem section_surjective (T : Type) [TopologicalSpace T] (n : ℕ) :
    Function.Surjective (sectionTransition ℓ T n) := by
  have h : Function.Surjective (reduction ℓ (Nat.le_succ n)) :=
    ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ n))
  let σ : ZMod (ℓ ^ n) → ZMod (ℓ ^ (n + 1)) := h.hasRightInverse.choose
  let hσ : Function.RightInverse σ (reduction ℓ (Nat.le_succ n)) :=
    h.hasRightInverse.choose_spec
  intro f
  refine ⟨⟨fun x ↦ σ (f x), continuous_of_discreteTopology.comp f.continuous⟩, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact hσ (f x)

variable (X : Scheme.{0}) (W : X.ProEt)

/-- The actual sheaf reduction is surjective on each of its native chart section groups. -/
theorem chart_surjective (n : ℕ) :
    Function.Surjective ((residueTransition X ℓ n).hom.app (op W)) :=
  section_surjective ℓ W.left n

/-- The actual sequential product difference is surjective on each chart's sections. -/
theorem chart_difference_surjective :
    Function.Surjective (productDifference
      (fun n ↦ (residueSheaf X ℓ n).obj.obj (op W))
      (fun n ↦ ((residueTransition X ℓ n).hom.app (op W)).hom)) :=
  productDifference_surjective _ _ (chart_surjective ℓ X W)

end
end ManuscriptAudit.ProetaleResidueChartSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleResidueChartSurjectivity.section_surjective,
      ``ManuscriptAudit.ProetaleResidueChartSurjectivity.chart_surjective,
      ``ManuscriptAudit.ProetaleResidueChartSurjectivity.chart_difference_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
