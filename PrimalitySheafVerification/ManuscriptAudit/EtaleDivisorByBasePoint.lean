import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Data.Finsupp.ToDFinsupp
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedPoints

/-!
# Divisor cycles grouped over the closed points of the base

A finite cycle on an integral affine étale chart is equivalently a
finitely supported family of functions on the finite fibers above the
height-one points of the base.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open IsDedekindDomain

noncomputable section

private def fiberFunctionEquiv {ι : Type*} [Finite ι] :
    (ι →₀ ℤ) ≃+ (ι → ℤ) :=
  { Finsupp.equivFunOnFinite with map_add' := fun _ _ ↦ rfl }

private def groupFiniteFibers {A B : Type*} (f : B → A) (h : ∀ a, Finite {b // f b = a}) :
    (B →₀ ℤ) ≃+ (Π₀ a, ({b // f b = a} → ℤ)) := by
  classical
  let e := Finsupp.domCongr (M := ℤ) (Equiv.sigmaFiberEquiv f).symm
  let k := DFinsupp.mapRange.addEquiv (fun a ↦ by
    letI := h a
    exact fiberFunctionEquiv (ι := {b // f b = a}))
  exact e.trans (sigmaFinsuppAddEquivDFinsupp.trans k)

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
