import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeFibers
import PrimalitySheafVerification.ManuscriptAudit.Paper6ArithmeticFiberBumps

/-! Exact ordinary binary étale cohomology bumps on the actual canonical
closed-point fibers of two fixed integral models, at every odd prime. -/

namespace ManuscriptAudit.IntegralOddPrimeBumps

open AlgebraicGeometry CategoryTheory
open IntegralOddPrimeFibers
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 7000
set_option maxHeartbeats 900000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime]

private abbrev R := ZMod 2
private abbrev C := AddCommGrpCat.{0}
private abbrev coeff := AddCommGrpCat.of R

abbrev H (S : Scheme.{0}) := Sheaf.H ((constantSheaf S.smallEtaleTopology C).obj coeff) 1

def binaryModule (S : Scheme.{0}) : Module R (H S) :=
  BinaryConstantCohomology.coefficientModule S.smallEtaleTopology 1

abbrev cuspSmooth := (cuspToResidue p).smoothLocus.toScheme
abbrev nodeSmooth := (nodeToResidue p).smoothLocus.toScheme

private theorem two_ne_zero (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd)

/-- In the actual cusp fiber at (p), degree-one dimensions of the whole
fiber and its genuine relative smooth open are one and two. -/
theorem cusp_finranks (hp : 2 < p) :
    letI := binaryModule (cuspFiber p)
    letI := binaryModule (cuspSmooth p)
    Module.finrank R (H (cuspFiber p)) = 1 ∧ Module.finrank R (H (cuspSmooth p)) = 2 := by
  letI := binaryModule (cuspFiber p)
  letI := binaryModule (cuspSmooth p)
  let e : R ≃+ H (cuspFiber p) :=
    (ArithmeticCuspBinary.cuspHOneEquiv (ZMod p) p (two_ne_zero p hp)).trans
      (schemeIsoCohomologyEquiv (cuspIso p).symm coeff 1)
  let g : (R × R) ≃+ H (cuspSmooth p) :=
    (ArithmeticCuspBinary.punctureHOneEquiv (ZMod p) (two_ne_zero p hp)).trans
      (schemeIsoCohomologyEquiv (cuspSmoothIso p).symm coeff 1)
  let eL : R ≃ₗ[R] H (cuspFiber p) := { e with map_smul' := ZMod.map_smul e }
  let gL : (R × R) ≃ₗ[R] H (cuspSmooth p) := { g with map_smul' := ZMod.map_smul g }
  refine ⟨eL.finrank_eq.symm.trans (CommSemiring.finrank_self _), ?_⟩
  rw [← gL.finrank_eq, Module.finrank_prod, CommSemiring.finrank_self] <;> norm_num

/-- The printed signed difference is negative on every odd-prime
canonical cusp fiber of the same flat integral model. -/
theorem cusp_signed_bump (hp : 2 < p) :
    letI := binaryModule (cuspFiber p)
    letI := binaryModule (cuspSmooth p)
    (Module.finrank R (H (cuspFiber p)) : ℤ) -
      Module.finrank R (H (cuspSmooth p)) = -1 := by
  letI := binaryModule (cuspFiber p)
  letI := binaryModule (cuspSmooth p)
  obtain ⟨h, h'⟩ := cusp_finranks p hp
  rw [h, h'] <;> norm_num

/-- Dimensions for the actual nodal fiber and its actual relative
smooth open, in the same coefficient convention. -/
theorem node_finranks (hp : 2 < p) :
    letI := binaryModule (nodalFiber p)
    letI := binaryModule (nodeSmooth p)
    Module.finrank R (H (nodalFiber p)) = 2 ∧ Module.finrank R (H (nodeSmooth p)) = 2 := by
  letI := binaryModule (nodalFiber p)
  letI := binaryModule (nodeSmooth p)
  letI := NodalArithmeticBump.properModule (ZMod p)
  letI := NodalArithmeticBump.smoothModule (ZMod p)
  let e := schemeIsoCohomologyEquiv (nodeIso p) coeff 1
  let g := schemeIsoCohomologyEquiv (nodeSmoothIso p) coeff 1
  let eL : H (nodalFiber p) ≃ₗ[R] NodalArithmeticProjectiveHOne.properHOne (ZMod p) :=
    { e with map_smul' := ZMod.map_smul e }
  let gL : H (nodeSmooth p) ≃ₗ[R] NodalArithmeticBump.smoothHOne (ZMod p) :=
    { g with map_smul' := ZMod.map_smul g }
  obtain ⟨h, h'⟩ := Paper6ArithmeticFiberBumps.node_finranks (ZMod p) (two_ne_zero p hp)
  exact ⟨eL.finrank_eq.trans h, gL.finrank_eq.trans h'⟩

/-- The canonical nodal fibers at every odd prime are nonsmooth
although their printed signed arithmetic bump is zero. -/
theorem node_zero_bump_and_nonsmooth (hp : 2 < p) :
    letI := binaryModule (nodalFiber p)
    letI := binaryModule (nodeSmooth p)
    ((Module.finrank R (H (nodalFiber p)) : ℤ) -
      Module.finrank R (H (nodeSmooth p)) = 0) ∧
      ¬ AlgebraicGeometry.Smooth (nodeToResidue p) := by
  letI := binaryModule (nodalFiber p)
  letI := binaryModule (nodeSmooth p)
  obtain ⟨h, h'⟩ := node_finranks p hp
  exact ⟨by rw [h, h', sub_self], node_not_smooth p⟩

end
end ManuscriptAudit.IntegralOddPrimeBumps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralOddPrimeBumps.cusp_finranks,
      ``ManuscriptAudit.IntegralOddPrimeBumps.cusp_signed_bump,
      ``ManuscriptAudit.IntegralOddPrimeBumps.node_finranks,
      ``ManuscriptAudit.IntegralOddPrimeBumps.node_zero_bump_and_nonsmooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
