import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleConstantHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportAbsoluteHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveCyclicHTwo
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.OpenComplementRationalPointCohomology

/-! Every native nodal compact cohomology group for an invertible cyclic coefficient order. -/

namespace ManuscriptAudit.NodalCompactSupportCyclicDegrees

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveCyclicHOne (C)
open NodalCompactSupportHOne (nodalHc nodalHcSuccProjectiveEquiv)
open NodalSmoothLocus (nodePoint)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open OpenEtaleExtension (extensionByZeroIdIso)
open OpenComplementRationalPointCohomology (extensionH positiveEquiv zero_subsingleton)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (d : ℕ)

private abbrev M := AddCommGrpCat.of (ZMod d)

/-- The actual compact cohomology of the proper model, using extension along its identity. -/
abbrev properHc (n : ℕ) := extensionH (𝟙 (projectiveNode K)) (M d) n

/-- The actual compact cohomology of the affine node in its proper compactification. -/
abbrev affineHc (n : ℕ) := nodalHc K (M d) n

/-- The actual compact cohomology of the relative smooth open in the proper node. -/
abbrev smoothHc (n : ℕ) := extensionH (smoothOpen K).ι (M d) n

private def trivialEquiv {A : Type} [AddCommGroup A] (h : Subsingleton A) : A ≃+ ZMod 1 where
  toFun := fun _ ↦ 0
  invFun := fun _ ↦ 0
  left_inv := fun x ↦ h.elim 0 x
  right_inv := fun x ↦ Subsingleton.elim 0 x
  map_add' := fun _ _ ↦ by rw [zero_add]

/-- Identity extension identifies the actual proper compact groups with ordinary cohomology. -/
def properOrdinaryComparison (n : ℕ) : properHc K d n ≃+ Sheaf.H (C (projectiveNode K) d) n := by
  let X := projectiveNode K
  let H := Sheaf.functorH X.smallEtaleTopology n
  exact (H.mapIso ((extensionByZeroIdIso X).app (C X d))).addCommGroupIsoToAddEquiv

variable [NeZero (d : K)]

/-- Ordinary cohomology of the proper model has one cyclic group in degrees zero, one and two. -/
def ordinaryEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Sheaf.H (C (projectiveNode K) d) n ≃+ ZMod (if n ≤ 2 then d else 1) := by
  cases n with
  | zero =>
    change Sheaf.H (C (projectiveNode K) d) 0 ≃+ ZMod d
    letI := NodalCompactSupportHZero.projectiveNode_irreducible K
    exact EtaleConstantHZero.constantHZeroEquiv (projectiveNode K) (M d) (nodePoint K)
  | succ n =>
    cases n with
    | zero =>
      change Sheaf.H (C (projectiveNode K) d) 1 ≃+ ZMod d
      exact NodalProjectiveCyclicHOne.projectiveHOneEquiv K d h2
    | succ n =>
      cases n with
      | zero =>
        change Sheaf.H (C (projectiveNode K) d) 2 ≃+ ZMod d
        exact NodalProjectiveCyclicHTwo.projectiveHTwoEquiv K d h2
      | succ n =>
        change Sheaf.H (C (projectiveNode K) d) (n + 3) ≃+
          ZMod (if n + 3 ≤ 2 then d else 1)
        rw [if_neg (by omega : ¬ n + 3 ≤ 2)]
        exact trivialEquiv (NodalCompactSupportAbsoluteHigher.projective_H_add_three_subsingleton K h2 d n)

private theorem positive_order (n : ℕ) :
    (if n + 1 ≤ 2 then d else 1) = (if n + 1 = 1 ∨ n + 1 = 2 then d else 1) := by
  have h : n + 1 ≤ 2 ↔ n + 1 = 1 ∨ n + 1 = 2 := by omega
  rw [h]

/-- On the genuine proper model, compact cohomology is cyclic in degrees zero, one and two. -/
def properEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    properHc K d n ≃+ ZMod (if n ≤ 2 then d else 1) :=
  (properOrdinaryComparison K d n).trans (ordinaryEquiv K d h2 n)

/-- Compact cohomology of the actual affine node is cyclic in degrees one and two. -/
def affineEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    affineHc K d n ≃+ ZMod (if n = 1 ∨ n = 2 then d else 1) := by
  cases n with
  | zero =>
    change affineHc K d 0 ≃+ ZMod 1
    exact trivialEquiv (NodalCompactSupportHZero.compact_HZero_subsingleton K (M d))
  | succ n =>
    exact (nodalHcSuccProjectiveEquiv K (M d) n).trans
      ((ordinaryEquiv K d h2 (n + 1)).trans (ZMod.ringEquivCongr (positive_order d n)).toAddEquiv)

/-- Compact cohomology of the actual relative smooth open is cyclic in degrees one and two. -/
def smoothEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    smoothHc K d n ≃+ ZMod (if n = 1 ∨ n = 2 then d else 1) := by
  letI := projectiveOrigin_closed K
  cases n with
  | zero =>
    change smoothHc K d 0 ≃+ ZMod 1
    letI := NodalCompactSupportHZero.projectiveNode_irreducible K
    exact trivialEquiv (zero_subsingleton (smoothOpen K).ι K (projectiveOrigin K)
      (smooth_range K) (M d))
  | succ n =>
    let e := positiveEquiv (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (M d) n
    exact e.trans
      ((ordinaryEquiv K d h2 (n + 1)).trans (ZMod.ringEquivCongr (positive_order d n)).toAddEquiv)

end
end ManuscriptAudit.NodalCompactSupportCyclicDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportCyclicDegrees.properOrdinaryComparison,
      ``ManuscriptAudit.NodalCompactSupportCyclicDegrees.ordinaryEquiv,
      ``ManuscriptAudit.NodalCompactSupportCyclicDegrees.properEquiv,
      ``ManuscriptAudit.NodalCompactSupportCyclicDegrees.affineEquiv,
      ``ManuscriptAudit.NodalCompactSupportCyclicDegrees.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
