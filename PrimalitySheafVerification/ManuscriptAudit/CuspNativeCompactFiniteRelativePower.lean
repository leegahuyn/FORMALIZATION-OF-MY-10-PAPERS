import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactAdicRelativePower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactHigher
import PrimalitySheafVerification.ManuscriptAudit.CuspGeometricFiniteCompactHTwo
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactFinitePullback

/-! The actual native compact-support pullback of the relative power map
is multiplication by its exponent on the finite constant coefficient
groups. In particular this computes the two compact degree-two groups'
relative Frobenius action over the geometric residue field. -/

namespace ManuscriptAudit.CuspNativeCompactFiniteRelativePower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenProetaleExtension (extensionByZero)
open ProetaleConstantRestriction (constant)
open CuspProperCompactification (affineOpen affineCusp)
open CuspNativeCompactSmoothHOne (smoothOpen)
open CuspRelativePowerMap (projectiveMap affineMap)
open CuspRelativePowerCartesian (affine_isPullback)
open CuspRelativePowerSmoothOpen (smoothMap smooth_isPullback)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)
open ProetaleOpenCompactCoefficientNaturality (discreteMap)
open ProetaleAdicCompactFinitePullback (constant_scalar)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable (K : Type) [Field K] [IsAlgClosed K] (m : ℕ) (hm : 2 ≤ m)

abbrev affineGroup (d : ℕ) := Sheaf.H ((extensionByZero (affineOpen K) A).obj
  (constant (affineCusp K) (ZMod d))) 2

abbrev smoothGroup (d : ℕ) := Sheaf.H ((extensionByZero (smoothOpen K) A).obj
  (constant (cuspPuncturedOpen K).toScheme (ZMod d))) 2

/-- Pullback on actual affine compact cohomology with finite constant coefficients. -/
def affinePullback (d : ℕ) : affineGroup K d →+ affineGroup K d :=
  discreteMap (projectiveMap K m hm) (affineMap K m hm) (affineOpen K) (affineOpen K)
    (affine_isPullback K m hm).flip (ZMod d) 2

/-- Pullback on actual smooth compact cohomology with finite constant coefficients. -/
def smoothPullback (d : ℕ) : smoothGroup K d →+ smoothGroup K d :=
  discreteMap (projectiveMap K m hm) (smoothMap K m hm) (smoothOpen K) (smoothOpen K)
    (smooth_isPullback K m hm).flip (ZMod d) 2

variable (p ℓ : ℕ)
  [hp : Fact p.Prime] [hchar : CharP K p] [Fact ℓ.Prime] [NeZero (ℓ : K)]

include p hp hchar in
set_option maxHeartbeats 7500000 in
/-- The relative power action on actual affine compact finite cohomology is its exponent. -/
theorem affine_scalar (r : ℕ) (x : affineGroup K (ℓ ^ r)) :
    affinePullback K m hm (ℓ ^ r) x = m • x :=
  constant_scalar (affineOpen K) ℓ r (projectiveMap K m hm) (affineMap K m hm)
    (affine_isPullback K m hm).flip 2 m (CuspNativeCompactHigher.affine_subsingleton K ℓ p 0)
    (CuspNativeCompactAdicRelativePower.affine_scalar K m hm p Fact.out hchar ℓ) x

include p hp hchar in
set_option maxHeartbeats 7500000 in
/-- The relative power action on actual smooth compact finite cohomology is its exponent. -/
theorem smooth_scalar (r : ℕ) (x : smoothGroup K (ℓ ^ r)) :
    smoothPullback K m hm (ℓ ^ r) x = m • x :=
  constant_scalar (smoothOpen K) ℓ r (projectiveMap K m hm) (smoothMap K m hm)
    (smooth_isPullback K m hm).flip 2 m (CuspNativeCompactHigher.smooth_subsingleton K ℓ p 0)
    (CuspNativeCompactAdicRelativePower.smooth_scalar K m hm p Fact.out hchar ℓ) x

section Geometric

variable (q l : ℕ) [Fact q.Prime] [Fact l.Prime]

private abbrev G := AlgebraicClosure (ZMod q)
private theorem prime_nonzero (h : l ≠ q) : NeZero (l : G q) :=
  ⟨fun hz ↦ h ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : l.Prime)).mp
    ((CharP.cast_eq_zero_iff (G q) q l).mp hz)).symm⟩

/-- On the manuscript's affine group over the geometric residue field,
the relative Frobenius pullback is multiplication by the residue characteristic. -/
theorem geometric_affine_frobenius (h : l ≠ q) (x : CuspGeometricFiniteCompactHTwo.affineGroup q l) :
    affinePullback (G q) q (Fact.out : q.Prime).two_le l x = q • x := by
  letI := prime_nonzero q l h
  have hs : ∀ y : affineGroup (G q) l,
      affinePullback (G q) q (Fact.out : q.Prime).two_le l y = q • y := by
    simpa only [pow_one] using (affine_scalar (G q) q (Fact.out : q.Prime).two_le q l 1)
  exact hs x

/-- On the manuscript's punctured group over the geometric residue field,
the relative Frobenius pullback is multiplication by the residue characteristic. -/
theorem geometric_smooth_frobenius (h : l ≠ q) (x : CuspGeometricFiniteCompactHTwo.smoothGroup q l) :
    smoothPullback (G q) q (Fact.out : q.Prime).two_le l x = q • x := by
  letI := prime_nonzero q l h
  have hs : ∀ y : smoothGroup (G q) l,
      smoothPullback (G q) q (Fact.out : q.Prime).two_le l y = q • y := by
    simpa only [pow_one] using (smooth_scalar (G q) q (Fact.out : q.Prime).two_le q l 1)
  exact hs x

end Geometric
end
end ManuscriptAudit.CuspNativeCompactFiniteRelativePower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeCompactFiniteRelativePower.affine_scalar,
      ``ManuscriptAudit.CuspNativeCompactFiniteRelativePower.smooth_scalar,
      ``ManuscriptAudit.CuspNativeCompactFiniteRelativePower.geometric_affine_frobenius,
      ``ManuscriptAudit.CuspNativeCompactFiniteRelativePower.geometric_smooth_frobenius] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
