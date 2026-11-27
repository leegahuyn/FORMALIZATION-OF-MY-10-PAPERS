import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspProperTwoBoundaryPoints
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPointOpenSections

/-! The smooth puncture has the actual adic Laurent class in native compact
degree two, using its two-point continuous support kernel. -/

namespace ManuscriptAudit.CuspNativeCompactSmoothAdicHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (overlapEquiv restrictEquiv)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin smoothOpen_range smoothOpen_quasiCompact)
open ProetaleAdicClosedPairSupport (support pairRestriction)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open ProetaleOpenKernelHOne (chart restrictionKernelIso kernel_HOne_subsingleton restrictionProduct_isZero)
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
private abbrev o := origin K
private abbrev F := support (o K) (z K) ℓ
private abbrev d := pairRestriction (o K) (z K) ℓ

local instance infinityClosed : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
local instance originClosed : IsClosedImmersion (o K) := properOrigin_closed K

private theorem affine_disjoint : Disjoint (Set.range (j K)) (Set.range (z K)) := by
  apply Set.disjoint_left.mpr
  intro x hx hi
  rw [← CuspInfinitySupport.affine_complement_eq_infinity K] at hi
  exact hi hx

private theorem overlap_origin : Disjoint (Set.range (l K)) (Set.range (o K)) :=
  CuspNativeCompactSmoothHTwoLower.overlap_disjoint_origin K

private theorem overlap_infinity : Disjoint (Set.range (l K)) (Set.range (z K)) :=
  (affine_disjoint K).mono_left (by
    rintro _ ⟨x, rfl⟩
    exact ⟨pullback.fst (j K) (k K) x, rfl⟩)

private theorem line_disjoint : Disjoint (Set.range (k K)) (Set.range (o K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
  let x := SmallEtaleGeometricBaseChange.cuspOrigin K z
  have hxy : j K x = k K y := hz
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := j K) (g := k K) x y hxy
  exact Set.disjoint_left.mp (overlap_origin K) ⟨p, rfl⟩ ⟨z, congrArg (j K) hp.symm⟩

private theorem chart_HOne {U : Scheme.{0}} (f : U ⟶ X K) [IsOpenImmersion f]
    (h : Subsingleton (U.EllAdicCohomology ℓ 1))
    (hlift : Function.Surjective ((d K ℓ).hom.app (Opposite.op (chart f)))) :
    Subsingleton (Sheaf.H ((restriction f A).obj (F K ℓ)) 1) := by
  let e := restrictEquiv K ℓ f
  exact kernel_HOne_subsingleton f (d K ℓ) hlift ⟨fun x y ↦ e.injective (h.elim _ _)⟩

private theorem chart_range {U : Scheme.{0}} (f : U ⟶ X K) [IsOpenImmersion f] :
    Set.range (chart f).hom = Set.range f := by
  change Set.range (𝟙 U ≫ f) = _
  rw [Category.id_comp]

private theorem affine_HOne : Subsingleton (Sheaf.H ((restriction (j K) A).obj (F K ℓ)) 1) := by
  letI : IsOpenImmersion (chart (j K)).hom := by
    change IsOpenImmersion (𝟙 _ ≫ j K)
    infer_instance
  apply chart_HOne K ℓ (j K) (CuspNativeProetaleAffineHOne.adic_HOne_subsingleton K ℓ)
  apply ProetaleAdicPointOpenSections.pair_surjective_off_second K ℓ (o K) (z K) (chart (j K))
  rw [chart_range]
  exact affine_disjoint K

private theorem line_HOne : Subsingleton (Sheaf.H ((restriction (k K) A).obj (F K ℓ)) 1) := by
  letI : IsOpenImmersion (chart (k K)).hom := by
    change IsOpenImmersion (𝟙 _ ≫ k K)
    infer_instance
  apply chart_HOne K ℓ (k K) (ProetaleAffineLineAdicHOne.adic_HOne_subsingleton K ℓ)
  apply ProetaleAdicPointOpenSections.pair_surjective_off_first K ℓ (o K) (z K) (chart (k K))
  rw [chart_range]
  exact line_disjoint K

private def supportOverlap :
    Sheaf.H ((restriction (l K) A).obj (F K ℓ)) 1 ≃+ ℤ_[ℓ] := by
  let h₀ := ProetaleDisjointClosedSupport.restriction_closed_isZero (o K) (l K) ℤ_[ℓ] (overlap_origin K)
  let h₁ := ProetaleDisjointClosedSupport.restriction_closed_isZero (z K) (l K) ℤ_[ℓ] (overlap_infinity K)
  let h := restrictionProduct_isZero (l K) (functionsOver ℤ_[ℓ] (o K)) (functionsOver ℤ_[ℓ] (z K)) h₀ h₁
  let e := restrictionKernelIso (l K) (d K ℓ) h
  exact (cohomologyIso (X := pullback (j K) (k K)) e 1).trans (overlapEquiv K ℓ)

private def supportInclusion : ℤ_[ℓ] →+ Sheaf.H (F K ℓ) 2 :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1).comp
    (supportOverlap K ℓ).symm.toAddMonoidHom

private theorem supportInclusion_injective : Function.Injective (supportInclusion K ℓ) :=
  (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1
    (affine_HOne K ℓ) (line_HOne K ℓ)).comp (supportOverlap K ℓ).symm.injective

abbrev compactHTwo :=
  Sheaf.H ((extensionByZero (smoothOpen K) A).obj (functions ℤ_[ℓ] _)) 2

private def comparison : compactHTwo K ℓ ≃+ Sheaf.H (F K ℓ) 2 := by
  letI : QuasiCompact (smoothOpen K) := smoothOpen_quasiCompact K
  exact cohomologyIso (X := X K)
    (ProetaleAdicClosedPairSupport.extensionKernelIso (o K) (z K) ℓ (smoothOpen K) (smoothOpen_range K)) 2

/-- The actual adic Laurent class injects into native compact degree two of the smooth puncture. -/
def inclusion : ℤ_[ℓ] →+ compactHTwo K ℓ :=
  (comparison K ℓ).symm.toAddMonoidHom.comp (supportInclusion K ℓ)

theorem inclusion_injective : Function.Injective (inclusion K ℓ) :=
  (comparison K ℓ).symm.injective.comp (supportInclusion_injective K ℓ)

end

end ManuscriptAudit.CuspNativeCompactSmoothAdicHTwoLower

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeCompactSmoothAdicHTwoLower.inclusion_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
