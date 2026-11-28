import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalFiniteCompactHTwoNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleProperNormalization

/-! Finite compact cohomology of the actual affine smooth node is
identified with cohomology on the actual proper normalization. -/

namespace ManuscriptAudit.NodalNativeFiniteCompactHTwoProper

open AlgebraicGeometry CategoryTheory
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (functions)

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [Finite M]

def normalizationEquiv (h₂ : (2 : K) ≠ 0) :
    NodalFiniteCompactHTwoNormalization.compact K M ≃+
      Sheaf.H (functions M (normalizedNode K)) 2 := by
  letI : (directImage (normalizationMap K) AddCommGrpCat.{1}).PreservesEpimorphisms :=
    ⟨fun α ↦ NodalProetaleProperNormalization.map_epi K h₂ α⟩
  exact NodalFiniteCompactHTwoNormalization.normalizationEquiv K M h₂

end
end ManuscriptAudit.NodalNativeFiniteCompactHTwoProper

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNativeFiniteCompactHTwoProper.normalizationEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
