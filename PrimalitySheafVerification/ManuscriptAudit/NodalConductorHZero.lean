import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSheafKernel
import Mathlib.Data.ZMod.Basic

/-! Global normalization functions have equal values at the two actual
conductor branches, and the conductor contributes its coefficient group. -/

namespace ManuscriptAudit.NodalConductorHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open SmallEtaleBaseChange
open NodalNormalizationFiber (affineNode affineLine affineNormalization)
open NodalAffineOrigin (originMap)
open NodalConductorSheafKernel (normalizationFunctions conductorFunctions branchDifference)
open NodalNormalizationEtaleFibers (Norm Conductor plus minus)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev C := AddCommGrpCat.of (ZMod 2)
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

private abbrev term := Scheme.Etale.mk (𝟙 (affineNode K))
private def termTerminal : IsTerminal (term K) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (affineNode K)

private def terminalPullbackIso {X : Scheme.{0}} (f : X ⟶ affineNode K) :
    ((etaleBaseChange f).obj (term K)).left ≅ X :=
  asIso (pullback.snd (𝟙 (affineNode K)) f)

private def conductorSectionsEquiv :
    (conductorFunctions K C).obj.obj (op (term K)) ≃+ C := by
  let e := terminalPullbackIso K (originMap K)
  let p := e.inv (IsLocalRing.closedPoint K)
  refine { toFun := fun s => (show ContinuousMap (Conductor K (term K)).left C from s) p
           invFun := ContinuousMap.const (Conductor K (term K)).left
           left_inv := ?_
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl }
  intro s
  apply ContinuousMap.ext
  intro q
  have he : p = q := e.hom.homeomorph.injective (Subsingleton.elim _ _)
  let s' : ContinuousMap (Conductor K (term K)).left C := s
  exact congrArg s' he

/-- The actual split conductor support has exactly one mod-two global label. -/
def conductorHZeroEquiv : Sheaf.H (conductorFunctions K C) 0 ≃+ ZMod 2 :=
  (Sheaf.H.equiv₀ _ (termTerminal K)).trans (conductorSectionsEquiv K)

private theorem terminal_difference_zero (s : (normalizationFunctions K C).obj.obj (op (term K))) :
    (branchDifference K C).hom.app (op (term K)) s = 0 := by
  let e := terminalPullbackIso K (affineNormalization K)
  let u : ContinuousMap (Norm K (term K)).left C := s
  let u' : ContinuousMap (affineLine K) C := u.comp ⟨e.inv, e.inv.continuous⟩
  letI : PreconnectedSpace (affineLine K) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Polynomial K)))
  have hu (x y : (Norm K (term K)).left) : u x = u y := by
    have h := TotallyDisconnectedSpace.eq_of_continuous u' u'.continuous (e.hom x) (e.hom y)
    change u (e.inv (e.hom x)) = u (e.inv (e.hom y)) at h
    change u ((e.hom ≫ e.inv) x) = u ((e.hom ≫ e.inv) y) at h
    rw [e.hom_inv_id] at h
    exact h
  apply ContinuousMap.ext
  intro p
  change u (plus K (term K) p) - u (minus K (term K) p) = 0
  rw [hu (plus K (term K) p) (minus K (term K) p), sub_self]

/-- The degree-zero comparison from the normalization to the conductor is zero. -/
theorem difference_HZero_eq_zero :
    Sheaf.H.map (branchDifference K C) 0 = 0 := by
  ext s
  change Sheaf.H.map (branchDifference K C) 0 s = 0
  apply (Sheaf.H.equiv₀ (conductorFunctions K C) (termTerminal K)).injective
  rw [← Sheaf.H.equiv₀_naturality, map_zero]
  exact terminal_difference_zero K _

end
end ManuscriptAudit.NodalConductorHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorHZero.conductorHZeroEquiv,
      ``ManuscriptAudit.NodalConductorHZero.difference_HZero_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
