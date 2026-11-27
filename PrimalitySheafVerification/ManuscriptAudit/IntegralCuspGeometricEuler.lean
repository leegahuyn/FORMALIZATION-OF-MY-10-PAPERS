import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspFiniteCohomology
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricFiber
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeBumps
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportScalar
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionIsoDomain

/-! Arithmetic ordinary and geometric compact-support comparisons on one fixed integral cusp. -/

namespace ManuscriptAudit.IntegralCuspGeometricEuler

open AlgebraicGeometry CategoryTheory
open IntegralCuspGeometricFiber (geometricFiber geometricSmoothOpen affineIso
  smoothPunctureIso affineCompactOpen smoothCompactOpen smoothCompactOpen_fac)
open IntegralNodalGeometricFiber (closureField)
open CuspProperCompactification (affineCusp affineOpen projectiveCusp)
open CuspCompactSupportSequence (cuspHc punctureHc)
open CuspFiniteCohomology (eulerThrough)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)
open NodalCompactSupportScalar (coefficient extensionModule)
open OpenEtaleExtension (extensionByZero extensionByZeroConstantIsoDomain)
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] CuspCompactSupportEuler.cuspModule CuspCompactSupportEuler.punctureModule

variable (p : ℕ) [Fact p.Prime]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{0}
private abbrev modelCoeff := AddCommGrpCat.of (ULift.{0} (ZMod ℓ))
private abbrev affineHc (n : ℕ) := extensionH (affineCompactOpen p) (coefficient ℓ) n
private abbrev smoothHc (n : ℕ) := extensionH (smoothCompactOpen p) (coefficient ℓ) n

private def affineModule (n : ℕ) : Module (ZMod ℓ) (affineHc p ℓ n) :=
  extensionModule ℓ (affineCompactOpen p) n

private def smoothModule (n : ℕ) : Module (ZMod ℓ) (smoothHc p ℓ n) :=
  extensionModule ℓ (smoothCompactOpen p) n

attribute [local instance] affineModule smoothModule

/-- Compact Betti dimensions of the actual geometric cusp fibre. -/
def affineBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (affineHc p ℓ n)

/-- Compact Betti dimensions of the actual relative smooth geometric cusp fibre. -/
def smoothBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (smoothHc p ℓ n)

private def coefficientIso : coefficient ℓ ≅ modelCoeff ℓ :=
  (show ZMod ℓ ≃+ ULift.{0} (ZMod ℓ) from
    { toFun := ULift.up, invFun := ULift.down, left_inv := fun _ ↦ rfl,
      right_inv := fun _ ↦ rfl, map_add' := fun _ _ ↦ rfl }).toAddCommGrpIso

private def scalarTransport {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extensionByZero j A).obj ((constantSheaf U.smallEtaleTopology A).obj (coefficient ℓ)) ≅
      (extensionByZero j A).obj ((constantSheaf U.smallEtaleTopology A).obj (modelCoeff ℓ)) :=
  (extensionByZero j A).mapIso ((constantSheaf U.smallEtaleTopology A).mapIso (coefficientIso ℓ))

private def extensionCongr {U X : Scheme.{0}} (j k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    extensionByZero j A ≅ extensionByZero k A := by
  subst k
  exact Iso.refl _

/-- Actual compact cohomology of the geometric pullback is the checked affine cusp computation. -/
def affineCohomologyEquiv (n : ℕ) :
    affineHc p ℓ n ≃+ cuspHc (closureField p) (modelCoeff ℓ) n := by
  let K := closureField p
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  let j := affineOpen K
  let a := extensionByZeroConstantIsoDomain (affineIso p).hom j (coefficient ℓ)
  let b := scalarTransport ℓ j
  let H := Sheaf.functorH (projectiveCusp K).smallEtaleTopology n
  exact (H.mapIso (a ≪≫ b)).addCommGroupIsoToAddEquiv

/-- Actual compact cohomology of the relative smooth locus is the checked puncture computation. -/
def smoothCohomologyEquiv (n : ℕ) :
    smoothHc p ℓ n ≃+ punctureHc (closureField p) (modelCoeff ℓ) n := by
  let K := closureField p
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  let j := (cuspPuncturedOpen K).ι ≫ affineOpen K
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion ((cuspPuncturedOpen K).ι ≫ affineOpen K))
  let i := (smoothPunctureIso p).hom
  letI : IsIso i := inferInstanceAs (IsIso (smoothPunctureIso p).hom)
  let M := (constantSheaf (geometricSmoothOpen p).toScheme.smallEtaleTopology A).obj (coefficient ℓ)
  let a := (extensionCongr (smoothCompactOpen p) (i ≫ j) (smoothCompactOpen_fac p)).app M
  let b := extensionByZeroConstantIsoDomain i j (coefficient ℓ)
  let c := scalarTransport ℓ j
  let H := Sheaf.functorH (projectiveCusp K).smallEtaleTopology n
  exact (H.mapIso (a ≪≫ b ≪≫ c)).addCommGroupIsoToAddEquiv

private def linearOfAddEquiv {E F : Type} [AddCommGroup E] [Module (ZMod ℓ) E]
    [AddCommGroup F] [Module (ZMod ℓ) F] (e : E ≃+ F) : E ≃ₗ[ZMod ℓ] F :=
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

private theorem affineBetti_eq (n : ℕ) :
    affineBetti p ℓ n = Module.finrank (ZMod ℓ) (cuspHc (closureField p) (modelCoeff ℓ) n) :=
  LinearEquiv.finrank_eq (linearOfAddEquiv ℓ (affineCohomologyEquiv p ℓ n))

private theorem smoothBetti_eq (n : ℕ) :
    smoothBetti p ℓ n = Module.finrank (ZMod ℓ) (punctureHc (closureField p) (modelCoeff ℓ) n) :=
  LinearEquiv.finrank_eq (linearOfAddEquiv ℓ (smoothCohomologyEquiv p ℓ n))

variable [NeZero (ℓ : closureField p)]

/-- The actual geometric cusp and its smooth open have compact Euler characteristics one and zero. -/
theorem geometric_euler (N : ℕ) (hN : 3 ≤ N) :
    eulerThrough (affineBetti p ℓ) N = 1 ∧ eulerThrough (smoothBetti p ℓ) N = 0 := by
  have ha : affineBetti p ℓ = fun n ↦
      Module.finrank (ZMod ℓ) (cuspHc (closureField p) (modelCoeff ℓ) n) := funext (affineBetti_eq p ℓ)
  have hs : smoothBetti p ℓ = fun n ↦
      Module.finrank (ZMod ℓ) (punctureHc (closureField p) (modelCoeff ℓ) n) := funext (smoothBetti_eq p ℓ)
  rw [ha, hs]
  exact CuspFiniteCohomology.complete_euler_sums (closureField p) p ℓ N hN

/-- At every odd prime of the fixed integral cusp, the arithmetic ordinary difference is minus one
while the compact Euler characteristics of its geometric fibre and its smooth open are one and zero. -/
theorem arithmetic_bump_and_geometric_euler (hp : 2 < p) (N : ℕ) (hN : 3 ≤ N) :
    letI := IntegralOddPrimeBumps.binaryModule (IntegralOddPrimeFibers.cuspFiber p)
    letI := IntegralOddPrimeBumps.binaryModule (IntegralOddPrimeBumps.cuspSmooth p)
    ((Module.finrank (ZMod 2) (IntegralOddPrimeBumps.H (IntegralOddPrimeFibers.cuspFiber p)) : ℤ) -
        Module.finrank (ZMod 2) (IntegralOddPrimeBumps.H (IntegralOddPrimeBumps.cuspSmooth p)) = -1) ∧
    (eulerThrough (affineBetti p ℓ) N = 1 ∧ eulerThrough (smoothBetti p ℓ) N = 0) :=
  ⟨IntegralOddPrimeBumps.cusp_signed_bump p hp, geometric_euler p ℓ N hN⟩

end
end ManuscriptAudit.IntegralCuspGeometricEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspGeometricEuler.affineCohomologyEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricEuler.smoothCohomologyEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricEuler.geometric_euler,
      ``ManuscriptAudit.IntegralCuspGeometricEuler.arithmetic_bump_and_geometric_euler] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
