import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Data.DFinsupp.Sigma
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedPoints

/-!
# Divisor cycles grouped over the closed points of the base

A finite cycle on an integral affine étale chart is equivalently a
finitely supported family of functions on the finite fibers above the
height-one points of the base.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open IsDedekindDomain
open scoped DirectSum

noncomputable section

private def fiberFunctionEquiv {ι : Type*} [Finite ι] :
    (Π₀ _ : ι, ℤ) ≃+ (ι → ℤ) := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact { DFinsupp.equivFunOnFintype with map_add' := fun _ _ ↦ rfl }

private def groupFiniteFibers {A B : Type*} (f : B → A) (h : ∀ a, Finite {b // f b = a}) :
    (B →₀ ℤ) ≃+ (Π₀ a, ({b // f b = a} → ℤ)) := by
  classical
  let e := Finsupp.domCongr (M := ℤ) (Equiv.sigmaFiberEquiv f).symm
  let g := (finsuppLEquivDirectSum ℤ ℤ (Σ a, {b // f b = a})).toAddEquiv
  let c : (Π₀ _ : (Σ a, {b // f b = a}), ℤ) ≃+ (Π₀ a, Π₀ _ : {b // f b = a}, ℤ) :=
    { DFinsupp.sigmaCurryEquiv with
      map_add' := fun _ _ ↦ DFinsupp.ext fun a ↦ DFinsupp.ext fun b ↦ rfl }
  let k := DFinsupp.mapRange.addEquiv (fun a ↦ by
    letI := h a
    exact fiberFunctionEquiv (ι := {b // f b = a}))
  exact e.trans (g.trans (c.trans k))

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.Etale A B]

/-- On the actual chart, collecting divisor coefficients over each base
height-one point gives a finitely supported family of functions. -/
def cyclesByBasePoint :
    (HeightOneSpectrum B →₀ ℤ) ≃+
      (Π₀ p : HeightOneSpectrum A, ({q : HeightOneSpectrum B // comap A B q = p} → ℤ)) :=
  groupFiniteFibers (comap A B) (finite_comap_fiber A B)

/-- The reindexing retains the coefficient of every actual height-one point. -/
theorem cyclesByBasePoint_apply (d : HeightOneSpectrum B →₀ ℤ) (p : HeightOneSpectrum A)
    (q : {q : HeightOneSpectrum B // comap A B q = p}) :
    cyclesByBasePoint A B d p q = d q.val :=
  rfl

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleClosedPoints.cyclesByBasePoint,
      ``ManuscriptAudit.AffineEtaleClosedPoints.cyclesByBasePoint_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
