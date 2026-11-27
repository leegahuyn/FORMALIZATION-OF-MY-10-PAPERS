import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleExactDirectImageCohomology
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleAcyclic
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationDirectImageExact
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyVanishingLeft

/-! The genuine split affine node has no cyclic étale cohomology in degree at least two. -/

namespace ManuscriptAudit.NodalAffineHigherCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalNormalizationFiber (A B affineNode affineLine affineNormalization)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open NodalConductorAbelianHZero (conductor_H_succ_subsingleton)
open NodalConductorSheafKernel (normalizationFunctions)
open EtaleContinuousMapSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev Ab := AddCommGrpCat.{0}

local instance (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- All ordinary cyclic étale cohomology groups of the native affine node vanish in degree at least two. -/
theorem affine_H_add_two_subsingleton (h2 : (2 : K) ≠ 0) (d : ℕ) [NeZero (d : K)]
    (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (affineNode K).smallEtaleTopology Ab).obj
      (AddCommGrpCat.of (ZMod d))) (n + 2)) := by
  let M := AddCommGrpCat.of (ZMod d)
  let ν := affineNormalization K
  let G := SmallEtaleBaseChange.directImage ν Ab
  letI : G.PreservesEpimorphisms := ⟨fun α hα ↦ by
    letI := hα
    exact NodalNormalizationDirectImageExact.map_epi K h2 α⟩
  let S := sequence K M
  let hS := sequence_shortExact K M h2
  let eNorm : Sheaf.H S.X₂ (n + 2) ≃+ Sheaf.H (continuousMapSheaf (affineLine K) M) (n + 2) :=
    AffineEtaleExactDirectImageCohomology.cohomologyEquiv (CommRingCat.of (A K))
      (CommRingCat.of (B K)) ν (continuousMapSheaf (affineLine K) M) (n + 2)
  let eLine := ((Sheaf.functorH (affineLine K).smallEtaleTopology (n + 2)).mapIso
    (constantSheafContinuousMapIso (affineLine K) M)).addCommGroupIsoToAddEquiv
  have hLine := AffineLineEtaleAcyclic.cyclic_H_succ_subsingleton K d (n + 1)
  have hNorm : Subsingleton (Sheaf.H S.X₂ (n + 2)) :=
    ⟨fun x y ↦ (eNorm.trans eLine.symm).injective (hLine.elim _ _)⟩
  have hZ : Subsingleton (Sheaf.H S.X₁ (n + 2)) :=
    SheafCohomologyVanishingLeft.H_succ_subsingleton S hS (n + 1)
      (conductor_H_succ_subsingleton K M n) hNorm
  let e := ((Sheaf.functorH (affineNode K).smallEtaleTopology (n + 2)).mapIso
    (constantSheafContinuousMapIso (affineNode K) M)).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.injective (hZ.elim _ _)⟩

end
end ManuscriptAudit.NodalAffineHigherCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalAffineHigherCohomology.affine_H_add_two_subsingleton
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
