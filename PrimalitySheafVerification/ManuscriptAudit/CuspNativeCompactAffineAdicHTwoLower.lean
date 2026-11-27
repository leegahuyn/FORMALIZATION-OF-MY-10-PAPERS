import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedSupportKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPointOpenSections
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointClosedSupport
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport

/-! The genuine native compact degree-two group of the affine cusp
contains the actual adic Laurent class. -/

namespace ManuscriptAudit.CuspNativeCompactAffineAdicHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspProperYChart (lineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (overlapEquiv restrictEquiv)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleOpenKernelHOne (chart restrictionKernelIso kernel_HOne_subsingleton)
open OpenProetaleExtension (extensionByZero restriction)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting connecting_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K
private abbrev z := infinityPoint K
private abbrev F := ProetaleClosedKernelLocalSupport.K (z K) ℤ_[ℓ]
private abbrev d := diagonal ℤ_[ℓ] (z K)

local instance infinityClosed : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K

private theorem complement : Set.range (j K) = (Set.range (z K))ᶜ := by
  rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]

private theorem overlap_disjoint : Disjoint (Set.range (l K)) (Set.range (z K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hi
  have ha : l K x ∈ Set.range (j K) := ⟨pullback.fst (j K) (k K) x, rfl⟩
  rw [complement K] at ha
  exact ha hi

private theorem chart_HOne {U : Scheme.{0}} (f : U ⟶ X K) [IsOpenImmersion f]
    (h : Subsingleton (U.EllAdicCohomology ℓ 1)) :
    Subsingleton (Sheaf.H ((restriction f A).obj (F K ℓ)) 1) := by
  let e := restrictEquiv K ℓ f
  letI : IsOpenImmersion (chart f).hom := by
    change IsOpenImmersion (𝟙 U ≫ f)
    infer_instance
  exact kernel_HOne_subsingleton f (d K ℓ)
    (ProetaleAdicPointOpenSections.diagonal_surjective K ℓ (z K) (chart f))
    ⟨fun x y ↦ e.injective (h.elim _ _)⟩

private def supportOverlap :
    Sheaf.H ((restriction (l K) A).obj (F K ℓ)) 1 ≃+ ℤ_[ℓ] :=
  (cohomologyIso (X := pullback (j K) (k K)) (restrictionKernelIso (l K) (d K ℓ)
    (ProetaleDisjointClosedSupport.restriction_closed_isZero (z K) (l K) ℤ_[ℓ]
      (overlap_disjoint K))) 1).trans (overlapEquiv K ℓ)

private def supportInclusion : ℤ_[ℓ] →+ Sheaf.H (F K ℓ) 2 :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1).comp
    (supportOverlap K ℓ).symm.toAddMonoidHom

private theorem supportInclusion_injective : Function.Injective (supportInclusion K ℓ) :=
  (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1
    (chart_HOne K ℓ (j K) (CuspNativeProetaleAffineHOne.adic_HOne_subsingleton K ℓ))
    (chart_HOne K ℓ (k K) (ProetaleAffineLineAdicHOne.adic_HOne_subsingleton K ℓ))).comp
    (supportOverlap K ℓ).symm.injective

abbrev compactHTwo :=
  Sheaf.H ((extensionByZero (j K) A).obj (functions ℤ_[ℓ] (affineCusp K))) 2

private def comparison : compactHTwo K ℓ ≃+ Sheaf.H (F K ℓ) 2 := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (j K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  letI : QuasiCompact (j K) := QuasiCompact.of_comp (j K) (projectiveCuspToBase K)
  exact cohomologyIso (X := X K)
    (ProetaleAdicClosedSupportKernel.extensionKernelIso (z K) (j K) ℓ (complement K)) 2

/-- The adic Laurent class injects into actual continuous compact degree two. -/
def inclusion : ℤ_[ℓ] →+ compactHTwo K ℓ :=
  (comparison K ℓ).symm.toAddMonoidHom.comp (supportInclusion K ℓ)

theorem inclusion_injective : Function.Injective (inclusion K ℓ) :=
  (comparison K ℓ).symm.injective.comp (supportInclusion_injective K ℓ)

end

end ManuscriptAudit.CuspNativeCompactAffineAdicHTwoLower

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeCompactAffineAdicHTwoLower.inclusion_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
