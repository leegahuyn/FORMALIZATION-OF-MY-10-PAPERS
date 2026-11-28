import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHigherCompact

/-! Higher native cohomology vanishing transfers from the actual
normalization to the proper node and its smooth affine compact group. -/

namespace ManuscriptAudit.NodalNativeHigherVanishing

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalAffineSmoothCompactOpen (compactOpen)
open OpenProetaleExtension (extensionByZero)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleAdicHOneDetection (finiteCoefficient)
open NodalNormalizedNativeHigher (residue_add_three_subsingleton adic_add_three_subsingleton)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h₂ : (2 : K) ≠ 0)
  (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

/-- The actual proper nodal group vanishes at every finite coefficient level in degree at least three. -/
theorem proper_residue_subsingleton (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (projectiveNode K) l r) (n + 3)) := by
  let e := NodalNativeHigherNormalization.discreteEquiv K (ZMod (l ^ r)) h₂ (n + 1)
  have h := residue_add_three_subsingleton K h₂ l r n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

/-- The proper curve has no genuine adic cohomology in these degrees. -/
theorem proper_adic_subsingleton (n : ℕ) :
    Subsingleton ((projectiveNode K).EllAdicCohomology l (n + 3)) := by
  let e := NodalNativeHigherNormalization.adicEquiv K l h₂ (n + 1)
  have h := adic_add_three_subsingleton K h₂ l n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

/-- The actual smooth affine compact-support adic cohomology also vanishes in degree at least three. -/
theorem compact_adic_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H ((extensionByZero (compactOpen K) AddCommGrpCat.{1}).obj
      (functions ℤ_[l] _)) (n + 3)) := by
  let e := NodalNativeAdicHigherCompact.normalizationEquiv K l h₂ (n + 1)
  have h := adic_add_three_subsingleton K h₂ l n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

end
end ManuscriptAudit.NodalNativeHigherVanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeHigherVanishing.proper_residue_subsingleton,
      ``ManuscriptAudit.NodalNativeHigherVanishing.proper_adic_subsingleton,
      ``ManuscriptAudit.NodalNativeHigherVanishing.compact_adic_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
