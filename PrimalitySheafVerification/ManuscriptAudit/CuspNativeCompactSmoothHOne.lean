import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportSequence
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary
import PrimalitySheafVerification.ManuscriptAudit.NativeSingularCurveCompactHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleNestedOpenBoundary
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHZero

/-! Native compact degree one of the actual punctured cusp, using its
origin and infinity in the checked proper compactification. -/

namespace ManuscriptAudit.CuspNativeCompactSmoothHOne

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (affineCusp affineOpen projectiveCusp projectiveCuspToBase)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open SmallEtaleGeometricBaseChange (cuspOrigin cuspOrigin_closedImmersion cuspPuncturedOpen)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{1}

private theorem punctured_range :
    Set.range (cuspPuncturedOpen K).ι = (Set.range (cuspOrigin K))ᶜ := by
  change ((cuspPuncturedOpen K).ι.opensRange : Set (affineCusp K)) = (Set.range (cuspOrigin K))ᶜ
  rw [Scheme.Opens.opensRange_ι]
  rfl

private theorem properOrigin_closed : IsClosedImmersion (cuspOrigin K ≫ affineOpen K) := by
  apply isClosedImmersion_of_comp_eq_id (projectiveCuspToBase K)
  have h : CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K)) ≫
      CuspConductorSquare.origin K = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Polynomial.constantCoeff : Polynomial K →+* K) (Polynomial.C a) = a
    simp
  rw [Category.assoc, CuspProperCompactification.affineOpen_toBase, cuspOrigin,
    ← Spec.map_comp, h, Spec.map_id]

/-- The displayed open is the actual composite of the punctured affine chart with its proper embedding. -/
abbrev smoothOpen : (cuspPuncturedOpen K).toScheme ⟶ projectiveCusp K :=
  (cuspPuncturedOpen K).ι ≫ affineOpen K

variable (d : ℕ) [NeZero (d : K)]

local instance cyclicTopology : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete : DiscreteTopology (ZMod d) := ⟨rfl⟩

private def rootValue : C(Spec (CommRingCat.of K), ZMod d) ≃+ ZMod d where
  toFun f := f (IsLocalRing.closedPoint K)
  invFun x := ContinuousMap.const _ x
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    exact congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The actual punctured cusp has one copy of the coefficient group in native
compact degree one, via the boundary of the actual rational origin. -/
def smoothHOneEquiv : NativeSingularCurveCompactHOne.compact d (smoothOpen K) ≃+ ZMod d := by
  let U := affineCusp K
  let X := projectiveCusp K
  let j := affineOpen K
  let V := (cuspPuncturedOpen K).toScheme
  let i := (cuspPuncturedOpen K).ι
  let o := cuspOrigin K
  let infinity := infinityPoint K
  let M := ZMod d
  let E := extensionByZero j A
  letI := cuspOrigin_closedImmersion K
  letI := properOrigin_closed K
  letI := infinityPoint_isClosedImmersion K
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  have h∞ : Set.range j = (Set.range infinity)ᶜ := by
    change Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  have h₀ : Subsingleton (Sheaf.H (E.obj (functions M U)) 0) :=
    ProetaleOpenClosedHZero.compactFunctionsHZero_subsingleton K infinity M j h∞
  let e := cohomologyIso (X := X) (E.mapIso (ProetaleDiscreteConstant.constantIso U M)) 1
  letI := NativeSingularCurveCompactHOne.cusp_affine_subsingleton K d
  have h₁ : Subsingleton (Sheaf.H (E.obj (functions M U)) 1) :=
    e.symm.injective.subsingleton
  let β := ProetaleNestedOpenBoundary.boundaryEquiv i j K o M (punctured_range K) h₀ h₁
  let c := (extensionByZero (i ≫ j) A).mapIso (ProetaleDiscreteConstant.constantIso V M)
  exact (cohomologyIso (X := X) c 1).trans
    (β.symm.trans ((HZeroEquiv M (o ≫ j)).trans (rootValue K d)))

end
end ManuscriptAudit.CuspNativeCompactSmoothHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeCompactSmoothHOne.smoothHOneEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
