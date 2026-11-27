import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricPrimePower
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoOverBase
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusUnderIso

/-! The proper, affine, and relative smooth loci on the literal nodal geometric fibre at (2). -/

namespace ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralNodalGeometricFiber (closureField geometricFiber geometricToBase)
open IntegralNodalGeometricPrimePower (geometricAffine geometricAffineOpen)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open CuspProperCompactification (affineCusp projectiveCusp projectiveCuspToBase)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev coefficientField := closureField 2
private abbrev K := coefficientField

/-- The literal geometric pullback of the proper integral nodal fibre at (2) is the proper cusp. -/
def cuspProjectiveIso : geometricFiber 2 ≅ projectiveCusp K :=
  IntegralNodalGeometricFiber.projectiveIso 2 ≪≫ NodalCharacteristicTwoProjective.projectiveIso K

theorem cuspProjectiveIso_over :
    cuspProjectiveIso.hom ≫ projectiveCuspToBase K = geometricToBase 2 := by
  change ((IntegralNodalGeometricFiber.projectiveIso 2).hom ≫
    (NodalCharacteristicTwoProjective.projectiveIso K).hom) ≫ projectiveCuspToBase K = _
  rw [Category.assoc, NodalCharacteristicTwoOverBase.projectiveIso_over,
    IntegralNodalGeometricFiber.projectiveIso_over]

/-- The actual pulled-back affine chart identifies with the affine cusp. -/
def cuspAffineIso : geometricAffine 2 ≅ affineCusp K := by
  let e := IntegralNodalGeometricFiber.projectiveIso 2
  let j := NodalProjectiveClosure.affineOpen K
  let i := pullback.snd e.hom j
  letI : IsIso i := inferInstanceAs (IsIso (pullback.snd
    (IntegralNodalGeometricFiber.projectiveIso 2).hom (NodalProjectiveClosure.affineOpen K)))
  exact asIso i ≪≫ (NodalCharacteristicTwoAffine.affineIso K).symm

/-- The affine comparison is a square of the displayed compactifying open immersions. -/
theorem cuspAffineIso_fac :
    geometricAffineOpen 2 ≫ cuspProjectiveIso.hom =
      cuspAffineIso.hom ≫ CuspProperCompactification.affineOpen K := by
  let e := IntegralNodalGeometricFiber.projectiveIso 2
  let f := NodalCharacteristicTwoProjective.projectiveIso K
  let g := (NodalCharacteristicTwoAffine.affineIso K).symm
  let j := NodalProjectiveClosure.affineOpen K
  let k := CuspProperCompactification.affineOpen K
  let i := pullback.snd e.hom j
  have h : geometricAffineOpen 2 ≫ e.hom = i ≫ j := pullback.condition
  change geometricAffineOpen 2 ≫ e.hom ≫ f.hom = (i ≫ g.hom) ≫ k
  calc
    _ = (geometricAffineOpen 2 ≫ e.hom) ≫ f.hom := (Category.assoc _ _ _).symm
    _ = (i ≫ j) ≫ f.hom := by rw [h]
    _ = i ≫ (j ≫ f.hom) := Category.assoc _ _ _
    _ = i ≫ (g.hom ≫ k) := by
      have hAff : j ≫ f.hom = g.hom ≫ k := NodalCharacteristicTwoOverBase.affine_square_on_closures K
      exact congrArg (fun a : NodalProjectiveClosure.affineNode K ⟶ projectiveCusp K ↦ i ≫ a) hAff
    _ = _ := (Category.assoc _ _ _).symm

private instance cuspToBase_finitePresentation :
    LocallyOfFinitePresentation (projectiveCuspToBase K) := by
  have h : cuspProjectiveIso.inv ≫ geometricToBase 2 = projectiveCuspToBase K := by
    rw [← cuspProjectiveIso_over, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

/-- The literal relative smooth open is identified with the relative smooth open of the proper cusp. -/
def cuspSmoothIso :
    (geometricSmoothOpen 2).toScheme ≅ (projectiveCuspToBase K).smoothLocus.toScheme :=
  SmoothLocusUnderIso.iso cuspProjectiveIso (geometricToBase 2)
    (projectiveCuspToBase K) cuspProjectiveIso_over

theorem cuspSmoothIso_fac :
    cuspSmoothIso.hom ≫ (projectiveCuspToBase K).smoothLocus.ι =
      (geometricSmoothOpen 2).ι ≫ cuspProjectiveIso.hom := by
  unfold cuspSmoothIso SmoothLocusUnderIso.iso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end
end ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspProjectiveIso,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspProjectiveIso_over,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspAffineIso,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspAffineIso_fac,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspSmoothIso,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry.cuspSmoothIso_fac] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
