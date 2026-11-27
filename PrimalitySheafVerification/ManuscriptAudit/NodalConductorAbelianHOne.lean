import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianSequence
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-! The actual geometric split affine node has one copy of every
invertible cyclic coefficient group in ordinary étale degree one. -/

namespace ManuscriptAudit.NodalConductorAbelianHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalNormalizationFiber (A B affineNode affineLine affineNormalization)
open NodalConductorAbelianHZero (conductorHZeroEquiv difference_HZero_eq_zero)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open NodalConductorSheafKernel (normalizationFunctions branchDifference)
open EtaleContinuousMapSheaf GeometricSkyscraperCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev Ab := AddCommGrpCat.{0}

variable (K : Type) [Field K]

private abbrev J := (affineNode K).smallEtaleTopology

section General

variable [IsSepClosed K]
variable (M : Ab) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

/-- The actual conductor connecting map computes affine H¹ when the
normalizing affine line has no positive classes in degree one. -/
def affineHOneEquiv_of_normalization (h2 : (2 : K) ≠ 0)
    (hLine : Subsingleton (Sheaf.H (continuousMapSheaf (affineLine K) M) 1)) :
    M ≃+ Sheaf.H ((constantSheaf (J K) Ab).obj M) 1 := by
  let S := sequence K M
  let hS := sequence_shortExact K M h2
  let Z := (constantSheaf (J K) Ab).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  let δ : Sheaf.H S.X₃ 0 →+ Sheaf.H S.X₁ 1 := hS.extClass.postcomp Z rfl
  have hδ_injective : Function.Injective δ := by
    have hKernel (x : Sheaf.H S.X₃ 0) (hx : δ x = 0) : x = 0 := by
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ Z hS x rfl hx
      change Sheaf.H.map (branchDifference K M) 0 y = x at hy
      rw [difference_HZero_eq_zero K M] at hy
      exact hy.symm
    intro x y h
    apply sub_eq_zero.mp
    apply hKernel
    rw [map_sub, h, sub_self]
  have hδ_surjective : Function.Surjective δ := by
    intro x
    have hN : Subsingleton (Sheaf.H (normalizationFunctions K M) 1) :=
      AffineEtaleMorphism.fullDirectImage_HOne_subsingleton
        (CommRingCat.of (A K)) (CommRingCat.of (B K)) (affineNormalization K)
        (continuousMapSheaf (affineLine K) M) hLine
    exact Ext.covariant_sequence_exact₁ Z hS x (hN.elim _ _) rfl
  let e := ((Sheaf.functorH (J K) 1).mapIso
    (constantSheafContinuousMapIso (affineNode K) M)).addCommGroupIsoToAddEquiv
  exact (conductorHZeroEquiv K M).symm.trans
    ((AddEquiv.ofBijective δ ⟨hδ_injective, hδ_surjective⟩).trans e.symm)

end General

variable [IsAlgClosed K]

local instance (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- With every cyclic coefficient order invertible in K, the actual
ordinary small étale H¹ of the split affine node is the coefficient group. -/
def affineCyclicHOneEquiv (h2 : (2 : K) ≠ 0) (d : ℕ) [NeZero (d : K)] :
    ZMod d ≃+ Sheaf.H ((constantSheaf (J K) Ab).obj (AddCommGrpCat.of (ZMod d))) 1 := by
  let M := AddCommGrpCat.of (ZMod d)
  let e := ((Sheaf.functorH (affineLine K).smallEtaleTopology 1).mapIso
    (constantSheafContinuousMapIso (affineLine K) M)).addCommGroupIsoToAddEquiv
  have h := SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K d
  exact affineHOneEquiv_of_normalization K M h2
    ⟨fun x y ↦ e.symm.injective (h.elim _ _)⟩

end

end ManuscriptAudit.NodalConductorAbelianHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorAbelianHOne.affineHOneEquiv_of_normalization,
      ``ManuscriptAudit.NodalConductorAbelianHOne.affineCyclicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
