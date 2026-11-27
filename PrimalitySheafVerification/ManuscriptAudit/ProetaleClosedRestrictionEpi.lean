import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallySurjective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants

/-! Actual restriction of discrete-valued native sections to a closed
subscheme is an epimorphism. Local lifts are constant on open charts. -/

namespace ManuscriptAudit.ProetaleClosedRestrictionEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedSupportLocalConstants

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 1200000 in
theorem restriction_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (diagonal M i).hom where
  imageSieve_mem {U} s := by
    classical
    choose W hW a ha using fun u : U.left ↦ exists_open_restriction_const i M U s u
    let V (u : U.left) := openObject U (W u)
    let f (u : U.left) : V u ⟶ U := openArrow U (W u)
    have hCover : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X U := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows V f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage U.left
      rw [Presieve.map_ofArrows]
      apply Scheme.etalePrecoverage_le_proetalePrecoverage _
      change Presieve.ofArrows (fun u ↦ (W u).toScheme) (fun u ↦ (W u).ι) ∈
        Scheme.precoverage @Etale U.left
      exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
        ⟨fun u ↦ ⟨u, ⟨u, hW u⟩, rfl⟩, fun _ ↦ inferInstance⟩
    apply (Scheme.ProEt.topology X).superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨u⟩
    refine ⟨⟨ContinuousMap.const (V u).left (a u)⟩, ?_⟩
    change (diagonal M i).hom.app (op (V u)) _ = (functionsOver M i).obj.map (f u).op s
    rw [ha u] <;> rfl

theorem restriction_epi : Epi (diagonal M i) := by
  letI : Sheaf.IsLocallySurjective (diagonal M i) := restriction_locallySurjective i M
  exact Sheaf.epi_of_isLocallySurjective (diagonal M i)

end
end ManuscriptAudit.ProetaleClosedRestrictionEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleClosedRestrictionEpi.restriction_epi
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
