import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.CuspOriginGeometricDirectImage
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSheafKernel

/-! The native global normalization-to-conductor map is zero, and the
geometric rational conductor term is the native skyscraper. -/

namespace ManuscriptAudit.NodalConductorAbelianHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange SmallEtaleGeometricBaseChange EtaleContinuousMapSheaf
open NodalNormalizationFiber (affineNode affineLine affineNormalization)
open NodalAffineOrigin (originMap)
open NodalConductorSheafKernel
open NodalNormalizationEtaleFibers (Norm Conductor plus minus)
open GeometricSkyscraperCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

variable (K : Type) [Field K]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev term := Scheme.Etale.mk (𝟙 (affineNode K))
private def termTerminal : IsTerminal (term K) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (affineNode K)

/-- The actual global branch difference of any section is zero. -/
theorem terminal_branch_difference_zero (s : (normalizationFunctions K M).obj.obj (op (term K))) :
    (branchDifference K M).hom.app (op (term K)) s = 0 := by
  let e : (Norm K (term K)).left ≅ affineLine K :=
    asIso (pullback.snd (𝟙 (affineNode K)) (affineNormalization K))
  let a : ContinuousMap (Norm K (term K)).left M := s
  let a' : ContinuousMap (affineLine K) M := a.comp ⟨e.inv, e.inv.continuous⟩
  letI : PreconnectedSpace (affineLine K) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Polynomial K)))
  have h (x y : (Norm K (term K)).left) : a x = a y := by
    have hxy := TotallyDisconnectedSpace.eq_of_continuous a' a'.continuous (e.hom x) (e.hom y)
    change a ((e.hom ≫ e.inv) x) = a ((e.hom ≫ e.inv) y) at hxy
    rw [e.hom_inv_id] at hxy
    exact hxy
  apply ContinuousMap.ext
  intro c
  change a (plus K (term K) c) - a (minus K (term K) c) = 0
  rw [h (plus K (term K) c) (minus K (term K) c), sub_self]

/-- Constant global normalization functions give equal branch values. -/
theorem difference_HZero_eq_zero :
    Sheaf.H.map (branchDifference K M) 0 = 0 := by
  ext s
  change Sheaf.H.map (branchDifference K M) 0 s = 0
  apply (Sheaf.H.equiv₀ (conductorFunctions K M) (termTerminal K)).injective
  rw [← Sheaf.H.equiv₀_naturality, map_zero]
  exact terminal_branch_difference_zero K M _

variable [IsSepClosed K]

/-- Over a separably closed field the actual conductor term is the
geometric skyscraper at the rational node. -/
def conductorSkyscraperIso :
    conductorFunctions K M ≅ (Scheme.pointSmallEtale (originMap K)).skyscraperSheaf M :=
  (directImage (originMap K) AddCommGrpCat.{0}).mapIso
      (constantSheafContinuousMapIso (Spec (CommRingCat.of K)) M).symm ≪≫
    rationalPointConstantDirectImageIso K (originMap K) M

/-- The conductor contributes precisely one copy of the coefficient group in degree zero. -/
def conductorHZeroEquiv : Sheaf.H (conductorFunctions K M) 0 ≃+ M :=
  (((Sheaf.functorH (affineNode K).smallEtaleTopology 0).mapIso
    (conductorSkyscraperIso K M)).addCommGroupIsoToAddEquiv).trans
    (geometricSkyscraperHZeroEquiv (Scheme.pointSmallEtale (originMap K)) M)

/-- The genuine geometric conductor sheaf has zero positive cohomology. -/
theorem conductor_H_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (conductorFunctions K M) (n + 1)) := by
  let e := ((Sheaf.functorH (affineNode K).smallEtaleTopology (n + 1)).mapIso
    (conductorSkyscraperIso K M)).addCommGroupIsoToAddEquiv
  have h := geometricSkyscraperH_succ_subsingleton (Scheme.pointSmallEtale (originMap K)) M n
  exact ⟨fun x y ↦ e.injective (h.elim _ _)⟩

end

end ManuscriptAudit.NodalConductorAbelianHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorAbelianHZero.terminal_branch_difference_zero,
      ``ManuscriptAudit.NodalConductorAbelianHZero.difference_HZero_eq_zero,
      ``ManuscriptAudit.NodalConductorAbelianHZero.conductorSkyscraperIso,
      ``ManuscriptAudit.NodalConductorAbelianHZero.conductorHZeroEquiv,
      ``ManuscriptAudit.NodalConductorAbelianHZero.conductor_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
