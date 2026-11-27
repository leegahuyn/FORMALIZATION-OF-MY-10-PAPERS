import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHZero
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricFiber
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary

/-! The genuine compactly supported native adic degree-zero groups of the
literal geometric fibers of the fixed integral cusp and its smooth open vanish. -/

namespace ManuscriptAudit.IntegralCuspNativeCompactAdicHZero

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField)
open IntegralCuspGeometricFiber (affineIso affineCompactOpen geometricSmoothOpen smoothCompactOpen)
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The native compact cohomology group with the actual continuous adic coefficients. -/
abbrev compactHZero {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (ℓ : ℕ) [Fact ℓ.Prime] :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (functions ℤ_[ℓ] U)) 0

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem affine_disjoint_infinity :
    Disjoint (Set.range (affineCompactOpen p)) (Set.range (infinityPoint (closureField p))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ h
  rw [← CuspInfinitySupport.affine_complement_eq_infinity (closureField p)] at h
  exact h ⟨(affineIso p).hom x, rfl⟩

private theorem smooth_disjoint_infinity :
    Disjoint (Set.range (smoothCompactOpen p)) (Set.range (infinityPoint (closureField p))) :=
  (affine_disjoint_infinity p).mono_left (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(geometricSmoothOpen p).ι x, rfl⟩)

theorem affine_subsingleton : Subsingleton (compactHZero (affineCompactOpen p) ℓ) := by
  let K := closureField p
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  letI := infinityPoint_isClosedImmersion K
  exact ProetaleAdicCompactHZero.compactHZero_subsingleton ℓ (affineCompactOpen p) K (infinityPoint K)
    (affine_disjoint_infinity p)

theorem smooth_subsingleton : Subsingleton (compactHZero (smoothCompactOpen p) ℓ) := by
  let K := closureField p
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  letI := infinityPoint_isClosedImmersion K
  exact ProetaleAdicCompactHZero.compactHZero_subsingleton ℓ (smoothCompactOpen p) K (infinityPoint K)
    (smooth_disjoint_infinity p)

end

end ManuscriptAudit.IntegralCuspNativeCompactAdicHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNativeCompactAdicHZero.affine_subsingleton,
      ``ManuscriptAudit.IntegralCuspNativeCompactAdicHZero.smooth_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
