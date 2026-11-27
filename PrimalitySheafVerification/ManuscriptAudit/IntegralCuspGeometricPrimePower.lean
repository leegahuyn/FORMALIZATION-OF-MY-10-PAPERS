import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricFiber
import PrimalitySheafVerification.ManuscriptAudit.OpenComplementRationalPointCohomology
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionIsoDomain

/-! Prime-power compactly supported cohomology of the actual geometric fibres of the integral cusp. -/

namespace ManuscriptAudit.IntegralCuspGeometricPrimePower

open AlgebraicGeometry CategoryTheory
open IntegralCuspGeometricFiber (geometricSmoothOpen affineIso smoothPunctureIso
  affineCompactOpen smoothCompactOpen smoothCompactOpen_fac)
open IntegralNodalGeometricFiber (closureField)
open CuspProperCompactification (affineOpen projectiveCusp)
open CuspCompactSupportSequence (cuspHc punctureHc)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)
open OpenEtaleExtension (extensionByZero extensionByZeroConstantIsoDomain)
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime]

private abbrev A := AddCommGrpCat.{0}

/-- Cohomology with actual extension by zero along the chosen proper compactification. -/
abbrev affineHc (d n : ℕ) :=
  extensionH (affineCompactOpen p) (AddCommGrpCat.of (ZMod d)) n

/-- Cohomology with actual extension by zero of the relative smooth locus. -/
abbrev smoothHc (d n : ℕ) :=
  extensionH (smoothCompactOpen p) (AddCommGrpCat.of (ZMod d)) n

private def extensionCongr {U X : Scheme.{0}} (j k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    extensionByZero j A ≅ extensionByZero k A := by
  subst k
  exact Iso.refl _

/-- Identify geometric pullback cohomology using the actual affine compactifying immersion. -/
def affineModelEquiv (d n : ℕ) : affineHc p d n ≃+ cuspHc (closureField p) (AddCommGrpCat.of (ZMod d)) n := by
  let K := closureField p
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  let e := extensionByZeroConstantIsoDomain (affineIso p).hom (affineOpen K) (AddCommGrpCat.of (ZMod d))
  exact ((Sheaf.functorH (projectiveCusp K).smallEtaleTopology n).mapIso e).addCommGroupIsoToAddEquiv

/-- Identify cohomology of the actual smooth geometric open using its compatible puncture immersion. -/
def smoothModelEquiv (d n : ℕ) :
    smoothHc p d n ≃+ punctureHc (closureField p) (AddCommGrpCat.of (ZMod d)) n := by
  let K := closureField p
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  let j := (cuspPuncturedOpen K).ι ≫ affineOpen K
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion ((cuspPuncturedOpen K).ι ≫ affineOpen K))
  let i := (smoothPunctureIso p).hom
  letI : IsIso i := inferInstanceAs (IsIso (smoothPunctureIso p).hom)
  let C := AddCommGrpCat.of (ZMod d)
  let M := (constantSheaf (geometricSmoothOpen p).toScheme.smallEtaleTopology A).obj C
  let a := (extensionCongr (smoothCompactOpen p) (i ≫ j) (smoothCompactOpen_fac p)).app M
  let b := extensionByZeroConstantIsoDomain i j C
  exact ((Sheaf.functorH (projectiveCusp K).smallEtaleTopology n).mapIso
    (a ≪≫ b)).addCommGroupIsoToAddEquiv

variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem primePower_two_le (r : ℕ) (hr : 1 ≤ r) : 2 ≤ ℓ ^ r := by
  cases r with
  | zero => omega
  | succ r =>
    rw [pow_succ]
    have hℓ : ℓ.Prime := Fact.out
    have hrPow : 1 ≤ ℓ ^ r := pow_pos hℓ.pos r
    exact hℓ.two_le.trans ((one_mul ℓ).symm.trans_le (Nat.mul_le_mul_right ℓ hrPow))

/-- Every prime-power order with a prime different from p is invertible on the geometric fibre. -/
theorem primePower_ne_zero (hℓp : ℓ ≠ p) (r : ℕ) : ((ℓ ^ r : ℕ) : closureField p) ≠ 0 := by
  have hℓ : (ℓ : closureField p) ≠ 0 := by
    intro h
    have hd : p ∣ ℓ := (CharP.cast_eq_zero_iff (closureField p) p ℓ).mp h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp hd).symm
  rw [Nat.cast_pow]
  exact pow_ne_zero r hℓ

/-- Hc groups of the fixed cusp's actual geometric fibre with ZMod (ℓ^r) for all degrees. -/
def affinePrimePowerEquiv (hℓp : ℓ ≠ p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    affineHc p (ℓ ^ r) n ≃+ ZMod (if n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨primePower_ne_zero p ℓ hℓp r⟩
  exact (affineModelEquiv p (ℓ ^ r) n).trans
    (CuspCompactSupportCyclicDegrees.cuspEquiv (closureField p) p (ℓ ^ r)
      (primePower_two_le ℓ r hr) n)

/-- Hc groups of its actual geometric relative smooth locus with ZMod (ℓ^r) for all degrees. -/
def smoothPrimePowerEquiv (hℓp : ℓ ≠ p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    smoothHc p (ℓ ^ r) n ≃+ ZMod (if n = 1 ∨ n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨primePower_ne_zero p ℓ hℓp r⟩
  exact (smoothModelEquiv p (ℓ ^ r) n).trans
    (CuspCompactSupportCyclicDegrees.punctureEquiv (closureField p) p (ℓ ^ r)
      (primePower_two_le ℓ r hr) n)

end
end ManuscriptAudit.IntegralCuspGeometricPrimePower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspGeometricPrimePower.affineModelEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricPrimePower.smoothModelEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricPrimePower.primePower_ne_zero,
      ``ManuscriptAudit.IntegralCuspGeometricPrimePower.affinePrimePowerEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricPrimePower.smoothPrimePowerEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
