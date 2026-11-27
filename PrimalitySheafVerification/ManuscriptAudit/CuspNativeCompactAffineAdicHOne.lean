import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedSupportKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Genuine native compact degree one for the affine cusp with
the actual continuous integral adic coefficients. -/

namespace ManuscriptAudit.CuspNativeCompactAffineAdicHOne

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp affineCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open OpenProetaleExtension (extensionByZero)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private theorem affineOpen_quasiCompact : QuasiCompact (affineOpen K) := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (affineOpen K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (affineOpen K) (projectiveCuspToBase K)

/-- Actual native compact degree one of the affine cusp is zero with
the true continuous adic coefficient sheaf. -/
theorem compact_HOne_subsingleton :
    Subsingleton (Sheaf.H ((extensionByZero (affineOpen K) AddCommGrpCat.{1}).obj
      (functions ℤ_[ℓ] (affineCusp K))) 1) := by
  let j := affineOpen K
  let i := infinityPoint K
  letI : IsClosedImmersion i := infinityPoint_isClosedImmersion K
  letI : QuasiCompact j := affineOpen_quasiCompact K
  have hComplement : Set.range j = (Set.range i)ᶜ := by
    change Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  let e := ProetaleAdicClosedSupportKernel.extensionKernelIso i j ℓ hComplement
  have hA : Subsingleton (Sheaf.H (functions ℤ_[ℓ] (projectiveCusp K)) 1) :=
    CuspNativeProetaleProperHOne.adic_HOne_subsingleton K ℓ
  let a := cohomologyIso (X := projectiveCusp K) e 1
  let b := ProetaleClosedAdicHOne.kernel_HOne_injective K i ℓ
  exact ⟨fun x y ↦ a.injective (b (hA.elim _ _))⟩

end

end ManuscriptAudit.CuspNativeCompactAffineAdicHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeCompactAffineAdicHOne.compact_HOne_subsingleton
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
