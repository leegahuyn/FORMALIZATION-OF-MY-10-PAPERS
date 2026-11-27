import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding
import PrimalitySheafVerification.ManuscriptAudit.BinaryExactCardinality
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationHOneComparison

/-! An arithmetic upper bound for the actual split affine node when its normalization has one arithmetic binary class. -/

namespace ManuscriptAudit.NodalArithmeticAffineBound

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalNormalizationFiber (A B affineNode affineLine affineNormalization)
open NodalConductorHZero (conductorHZeroEquiv)
open NodalConductorSequence (sequence sequence_shortExact)
open NodalConductorSheafKernel (normalizationFunctions)
open EtaleContinuousMapSheaf SmallEtaleCohomologyComparison

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] fullSiteHasExt

variable (K : Type) [Field K]
private abbrev M := AddCommGrpCat.of (ZMod 2)
private abbrev C := AddCommGrpCat.{0}
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

private abbrev F := continuousMapSheaf (affineLine K) M
abbrev affineHOne :=
  Sheaf.H ((constantSheaf (affineNode K).smallEtaleTopology C).obj M) 1

private theorem normalizationLabel
    (hLine : ZMod 2 ≃+ NodalNormalizationHOneComparison.normalizationHOne K) :
    ∃ p : Sheaf.H (normalizationFunctions K M) 1 →+ ZMod 2, Function.Injective p := by
  obtain ⟨q, hq⟩ := AffineEtaleDirectImageHOneEmbedding.HOne_embedding
    (CommRingCat.of (A K)) (CommRingCat.of (B K)) (affineNormalization K) (F K)
  let e := ((Sheaf.functorH (affineLine K).smallEtaleTopology 1).mapIso
    (constantSheafContinuousMapIso (affineLine K) M)).addCommGroupIsoToAddEquiv
  let label : ZMod 2 ≃+ Sheaf.H (F K) 1 :=
    hLine.trans e
  exact ⟨label.symm.toAddMonoidHom.comp q, label.symm.injective.comp hq⟩

/-- Actual ordinary arithmetic étale H¹ of the split affine node over F₅
with mod-two coefficients is finite with at most four elements. -/
theorem finite_card_le_four (h2 : (2 : K) ≠ 0)
    (hLine : ZMod 2 ≃+ NodalNormalizationHOneComparison.normalizationHOne K) :
    Finite (affineHOne K) ∧ Nat.card (affineHOne K) ≤ 4 := by
  let S := sequence K
  let hS := sequence_shortExact K h2
  let I := (constantSheaf (affineNode K).smallEtaleTopology C).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  let δ : ZMod 2 →+ Sheaf.H S.X₁ 1 :=
    (hS.extClass.postcomp I rfl).comp (conductorHZeroEquiv K).symm.toAddMonoidHom
  obtain ⟨r, hr⟩ := normalizationLabel K hLine
  let p : Sheaf.H S.X₁ 1 →+ ZMod 2 := r.comp (Sheaf.H.map S.f 1)
  have hKernel : ∀ x, p x = 0 → ∃ a, δ a = x := by
    intro x hx
    have hf : Sheaf.H.map S.f 1 x = 0 := hr (hx.trans (map_zero r).symm)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ I hS x hf (n₀ := 0) rfl
    refine ⟨conductorHZeroEquiv K y, ?_⟩
    change (hS.extClass.postcomp I rfl) ((conductorHZeroEquiv K).symm (conductorHZeroEquiv K y)) = x
    rw [AddEquiv.symm_apply_apply]
    exact hy
  obtain ⟨hF, hcard⟩ := BinaryExactCardinality.finite_card_le_four δ p hKernel
  let e : affineHOne K ≃+ Sheaf.H S.X₁ 1 :=
    ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    (constantSheafContinuousMapIso (affineNode K) M)).addCommGroupIsoToAddEquiv
  letI : Finite (Sheaf.H S.X₁ 1) := hF
  exact ⟨Finite.of_injective e e.injective, (Nat.card_congr e.toEquiv).trans_le hcard⟩

end
end ManuscriptAudit.NodalArithmeticAffineBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalArithmeticAffineBound.finite_card_le_four
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
