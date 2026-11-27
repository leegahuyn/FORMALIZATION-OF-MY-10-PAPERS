import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorSequence

/-! Rational-origin global sections and the actual zero branch
difference on the connected polynomial normalization chart. -/

namespace ManuscriptAudit.NodalProetaleConductorHZero

open AlgebraicGeometry CategoryTheory
open NodalProjectiveNormalization (normalizationMap)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalNormalizedNativeCharts (zToNormalized)
open NodalNormalizationBranches (branchMap)
open NodalProetaleConductorBinary (plus minus plus_over minus_over)
open NodalProetaleConductorSequence (sequence)
open ProetaleContinuousDirectImageMaps (functionsOver restriction)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv HZeroEquiv_restriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private def originEval : C(Spec (CommRingCat.of K), M) ≃+ M where
  toFun f := f (IsLocalRing.closedPoint K)
  invFun := ContinuousMap.const _
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    exact congrArg f (Subsingleton.elim (IsLocalRing.closedPoint K) x)
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Actual degree zero of the origin direct image is the coefficient group. -/
def originHZeroEquiv : Sheaf.H (functionsOver M (projectiveOrigin K)) 0 ≃+ M :=
  (HZeroEquiv M (projectiveOrigin K)).trans (originEval K M)

variable [DiscreteTopology M]

/-- Every global normalization section gives the same value on both
branches, since both branch maps factor through the polynomial chart. -/
theorem difference_HZero_eq_zero (h2 : (2 : K) ≠ 0)
    (a : Sheaf.H (functionsOver M (normalizationMap K)) 0) :
    Sheaf.H.map (sequence K h2 M).g 0 a = 0 := by
  let r₀ := restriction M (plus K h2) (plus_over K h2)
  let r₁ := restriction M (minus K h2) (minus_over K h2)
  change Sheaf.H.map (r₀ - r₁) 0 a = 0
  apply add_right_cancel (b := Sheaf.H.map r₁ 0 a)
  rw [← Sheaf.H.map_add_apply, sub_add_cancel, zero_add]
  apply (HZeroEquiv M (projectiveOrigin K)).injective
  simp only [HZeroEquiv_restriction, r₀, r₁]
  apply ContinuousMap.ext
  intro x
  let f := HZeroEquiv M (normalizationMap K) a
  let e := zToNormalized K h2
  let s : C(Spec (CommRingCat.of (Polynomial K)), M) := f.comp ⟨e, e.continuous⟩
  change s (branchMap K 1 x) = s (branchMap K (-1) x)
  exact TotallyDisconnectedSpace.eq_of_continuous s s.continuous _ _

end
end ManuscriptAudit.NodalProetaleConductorHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProetaleConductorHZero.originHZeroEquiv,
      ``ManuscriptAudit.NodalProetaleConductorHZero.difference_HZero_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
