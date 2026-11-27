import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHZero

/-! Degree zero of genuine native compactly supported continuous adic
coefficients on the affine cusp and its actual smooth puncture. -/

namespace ManuscriptAudit.CuspNativeCompactAdicHZero

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeCompactSmoothHOne (smoothOpen)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}

private theorem affine_disjoint_infinity :
    Disjoint (Set.range (affineOpen K)) (Set.range (infinityPoint K)) := by
  rw [← CuspInfinitySupport.affine_complement_eq_infinity K]
  exact disjoint_compl_right

private theorem smooth_disjoint_infinity :
    Disjoint (Set.range (smoothOpen K)) (Set.range (infinityPoint K)) :=
  (affine_disjoint_infinity K).mono_left (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(SmallEtaleGeometricBaseChange.cuspPuncturedOpen K).ι x, rfl⟩)

/-- The actual native compact degree-zero group of the affine cusp is zero. -/
theorem affine_subsingleton :
    Subsingleton (Sheaf.H ((extensionByZero (affineOpen K) A).obj (functions ℤ_[ℓ] _)) 0) := by
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  letI := infinityPoint_isClosedImmersion K
  exact ProetaleAdicCompactHZero.compactHZero_subsingleton ℓ (affineOpen K) K (infinityPoint K)
    (affine_disjoint_infinity K)

/-- The actual native compact degree-zero group of the smooth puncture is zero. -/
theorem smooth_subsingleton :
    Subsingleton (Sheaf.H ((extensionByZero (smoothOpen K) A).obj (functions ℤ_[ℓ] _)) 0) := by
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  letI := infinityPoint_isClosedImmersion K
  exact ProetaleAdicCompactHZero.compactHZero_subsingleton ℓ (smoothOpen K) K (infinityPoint K)
    (smooth_disjoint_infinity K)

end

end ManuscriptAudit.CuspNativeCompactAdicHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactAdicHZero.affine_subsingleton,
      ``ManuscriptAudit.CuspNativeCompactAdicHZero.smooth_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
