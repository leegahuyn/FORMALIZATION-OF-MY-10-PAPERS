import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoBranchKernel

/-! Continuous additive coefficient maps commute with the actual
normalization diagonal and the ordered branch difference. -/

namespace ManuscriptAudit.ProetaleContinuousCoefficientNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal restriction)
open ProetaleContinuousDirectImageGlobal (terminalEquiv finalObject HZeroEquiv)
open ProetaleTwoBranchKernel (sequence difference)
open ProetaleBaseChange (directImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
variable (f : M →+ N) (hf : Continuous f)

abbrev map (T : Scheme.{0}) : functions M T ⟶ functions N T :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).map (ProetaleResidueSheaves.coefficientMap T f hf)

abbrev mapOver {Y Z : Scheme.{0}} (p : Y ⟶ Z) : functionsOver M p ⟶ functionsOver N p :=
  (directImage p AddCommGrpCat.{1}).map (map f hf Y)

theorem diagonal_natural {Y Z : Scheme.{0}} (p : Y ⟶ Z) :
    map f hf Z ≫ diagonal N p = diagonal M p ≫ mapOver f hf p := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

theorem restriction_natural {O Y Z : Scheme.{0}} {p : Y ⟶ Z} {q : O ⟶ Z}
    (b : O ⟶ Y) (hb : b ≫ p = q) :
    mapOver f hf p ≫ restriction N b hb = restriction M b hb ≫ mapOver f hf q := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

/-- The actual morphism of diagonal/branch-difference short complexes. -/
def sequenceMap {O Y Z : Scheme.{0}} (p : Y ⟶ Z) (q : O ⟶ Z)
    (b₀ b₁ : O ⟶ Y) (h₀ : b₀ ≫ p = q) (h₁ : b₁ ≫ p = q) :
    sequence p q b₀ b₁ h₀ h₁ M ⟶ sequence p q b₀ b₁ h₀ h₁ N where
  τ₁ := map f hf Z
  τ₂ := mapOver f hf p
  τ₃ := mapOver f hf q
  comm₁₂ := diagonal_natural f hf p
  comm₂₃ := by
    change mapOver f hf p ≫ difference p q b₀ b₁ h₀ h₁ N =
      difference p q b₀ b₁ h₀ h₁ M ≫ mapOver f hf q
    rw [difference, difference, Preadditive.comp_sub, Preadditive.sub_comp,
      restriction_natural f hf b₀ h₀, restriction_natural f hf b₁ h₁]

/-- The native global coefficient map is literal postcomposition
with the continuous additive coefficient arrow. -/
theorem HZeroEquiv_mapOver {Y Z : Scheme.{0}} (p : Y ⟶ Z)
    (x : Sheaf.H (functionsOver M p) 0) (y : Y) :
    HZeroEquiv N p (Sheaf.H.map (mapOver f hf p) 0 x) y = f (HZeroEquiv M p x y) := by
  change terminalEquiv N p ((Sheaf.H.equiv₀ _
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale Z))
      (Sheaf.H.map (mapOver f hf p) 0 x)) y = _
  rw [← Sheaf.H.equiv₀_naturality]
  rfl

end
end ManuscriptAudit.ProetaleContinuousCoefficientNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleContinuousCoefficientNaturality.sequenceMap,
      ``ManuscriptAudit.ProetaleContinuousCoefficientNaturality.HZeroEquiv_mapOver] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
