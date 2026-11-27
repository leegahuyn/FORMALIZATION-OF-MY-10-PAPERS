import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees

/-! Finite cyclic and odd-prime-power compact cohomology of the literal nodal geometric fibre at (2). -/

namespace ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology

open AlgebraicGeometry CategoryTheory
open IntegralNodalCharacteristicTwoGeometry (coefficientField)
open IntegralNodalGeometricPrimePower (properHc affineHc smoothHc properModelEquiv affineModelEquiv
  smoothPositiveModelEquiv smoothHZero_subsingleton)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open OpenComplementRationalPointCohomology (positiveEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev K := coefficientField
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

variable (d : ℕ) [NeZero (d : K)]

/-- Cyclic compact cohomology of the literal proper geometric pullback of the fibre at (2). -/
def properEquiv (n : ℕ) : properHc 2 d n ≃+ ZMod (if n = 0 ∨ n = 2 then d else 1) :=
  (properModelEquiv 2 d n).trans (NodalCharacteristicTwoCyclicDegrees.ordinaryEquiv K d n)

/-- Cyclic compact cohomology of the actual affine chart in the geometric pullback at (2). -/
def affineEquiv (n : ℕ) : affineHc 2 d n ≃+ ZMod (if n = 2 then d else 1) :=
  (affineModelEquiv 2 d n).trans (NodalCharacteristicTwoCyclicDegrees.affineEquiv K d n)

/-- Cyclic compact cohomology of the actual relative smooth open of the geometric fibre at (2). -/
def smoothEquiv (n : ℕ) : smoothHc 2 d n ≃+ ZMod (if n = 2 then d else 1) := by
  cases n with
  | zero =>
    change smoothHc 2 d 0 ≃+ ZMod 1
    let h := smoothHZero_subsingleton 2 d
    exact AddEquiv.ofBijective (0 : smoothHc 2 d 0 →+ ZMod 1)
      ⟨fun x y _ ↦ h.elim x y, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩
  | succ n =>
    letI := projectiveOrigin_closed K
    let e := positiveEquiv (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (M d) n
    exact (smoothPositiveModelEquiv 2 d n).trans (e.symm.trans
      (NodalCharacteristicTwoCyclicDegrees.smoothEquiv K d (n + 1)))

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Every power of a prime distinct from two is invertible on the geometric fibre. -/
theorem power_ne_zero (hℓ₂ : ℓ ≠ 2) (r : ℕ) : ((ℓ ^ r : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero r (IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂)

def properPrimePowerEquiv (hℓ₂ : ℓ ≠ 2) (r n : ℕ) :
    properHc 2 (ℓ ^ r) n ≃+ ZMod (if n = 0 ∨ n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : K) := ⟨power_ne_zero ℓ hℓ₂ r⟩
  exact properEquiv (ℓ ^ r) n

def affinePrimePowerEquiv (hℓ₂ : ℓ ≠ 2) (r n : ℕ) :
    affineHc 2 (ℓ ^ r) n ≃+ ZMod (if n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : K) := ⟨power_ne_zero ℓ hℓ₂ r⟩
  exact affineEquiv (ℓ ^ r) n

def smoothPrimePowerEquiv (hℓ₂ : ℓ ≠ 2) (r n : ℕ) :
    smoothHc 2 (ℓ ^ r) n ≃+ ZMod (if n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : K) := ⟨power_ne_zero ℓ hℓ₂ r⟩
  exact smoothEquiv (ℓ ^ r) n

end
end ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.properEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.affineEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.smoothEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.power_ne_zero,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.properPrimePowerEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.affinePrimePowerEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology.smoothPrimePowerEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
