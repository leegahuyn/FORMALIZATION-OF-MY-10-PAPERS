import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationHOneComparison
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDirectImageHOne

/-! The ordinary small étale H¹ of the actual split affine nodal curve
with constant mod-two coefficients is exactly Z/2. -/

namespace ManuscriptAudit.NodalConductorHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalNormalizationFiber (A B affineNode affineLine affineNormalization)
open NodalConductorHZero (conductorHZeroEquiv difference_HZero_eq_zero)
open NodalConductorSequence (sequence sequence_shortExact)
open NodalConductorSheafKernel (baseFunctions normalizationFunctions branchDifference)
open EtaleContinuousMapSheaf
open SmallEtaleCohomologyComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev C := AddCommGrpCat.of (ZMod 2)
private abbrev J := (affineNode K).smallEtaleTopology
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
private abbrev F := continuousMapSheaf (affineLine K) C

private theorem normalizationPushforward_HOne_subsingleton (h2 : (2 : K) ≠ 0) :
    Subsingleton (Sheaf.H (normalizationFunctions K C) 1) := by
  let e := (Sheaf.functorH (affineLine K).smallEtaleTopology 1).mapIso
    (constantSheafContinuousMapIso (affineLine K) C)
  have hN := NodalNormalizationHOneComparison.normalization_HOne_subsingleton K h2
  have h : Subsingleton (Sheaf.H (F K) 1) := by
    constructor
    intro x y
    apply e.addCommGroupIsoToAddEquiv.symm.injective
    exact hN.allEq _ _
  exact AffineEtaleMorphism.fullDirectImage_HOne_subsingleton
    (CommRingCat.of (A K)) (CommRingCat.of (B K)) (affineNormalization K) (F K) h

/-- The actual connecting homomorphism identifies the affine nodal
H¹ with its single conductor label. -/
def affineHOneEquiv (h2 : (2 : K) ≠ 0) :
    ZMod 2 ≃+ NodalNormalizationHOneComparison.nodeHOne K := by
  let S := sequence K
  let hS := sequence_shortExact K h2
  let I := (constantSheaf (J K) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  let δ : Sheaf.H S.X₃ 0 →+ Sheaf.H S.X₁ 1 := hS.extClass.postcomp I rfl
  have δ_inj : Function.Injective δ := by
    have hzero (x : Sheaf.H S.X₃ 0) (hx : δ x = 0) : x = 0 := by
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ I hS x rfl hx
      change Sheaf.H.map (branchDifference K C) 0 y = x at hy
      rw [difference_HZero_eq_zero] at hy
      exact hy.symm
    intro x y h
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, h, sub_self]
  have δ_surj : Function.Surjective δ := by
    intro x
    letI : Subsingleton (Sheaf.H S.X₂ 1) := normalizationPushforward_HOne_subsingleton K h2
    exact Ext.covariant_sequence_exact₁ I hS x (Subsingleton.elim _ _) rfl
  let e := (Sheaf.functorH (J K) 1).mapIso (constantSheafContinuousMapIso (affineNode K) C)
  exact (conductorHZeroEquiv K).symm.trans
    ((AddEquiv.ofBijective δ ⟨δ_inj, δ_surj⟩).trans e.addCommGroupIsoToAddEquiv.symm)

end
end ManuscriptAudit.NodalConductorHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalConductorHOne.affineHOneEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
