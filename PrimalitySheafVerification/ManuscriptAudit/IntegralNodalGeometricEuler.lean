import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricBoundary
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeBumps
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothEulerComparison
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! Ordinary arithmetic fibre jumps and geometric compact Euler sums on the same fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalGeometricEuler

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber
open IntegralNodalGeometricBoundary
open NodalProjectiveClosure (projectiveNode)
open NodalCompactSupportScalar (coefficient ordinaryModule extensionModule)
open OpenEtaleExtension (extensionByZeroIdIso)
open OpenComplementRationalPointCohomology (extensionH positiveEquiv zero_subsingleton)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)
open scoped BigOperators

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{0}
private abbrev ordinaryH (X : Scheme.{0}) (n : ℕ) :=
  Sheaf.H ((constantSheaf X.smallEtaleTopology A).obj (coefficient ℓ)) n
private abbrev properHc (n : ℕ) := extensionH (𝟙 (geometricFiber p)) (coefficient ℓ) n
private abbrev smoothHc (n : ℕ) := extensionH (geometricSmoothOpen p).ι (coefficient ℓ) n

private def properCompactModule (n : ℕ) : Module (ZMod ℓ) (properHc p ℓ n) :=
  extensionModule ℓ (𝟙 (geometricFiber p)) n

private def smoothCompactModule (n : ℕ) : Module (ZMod ℓ) (smoothHc p ℓ n) :=
  extensionModule ℓ (geometricSmoothOpen p).ι n

attribute [local instance] properCompactModule smoothCompactModule

/-- Compact Betti dimensions of the actual geometric fibre, using the identity compactification. -/
def properBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (properHc p ℓ n)

/-- Compact Betti dimensions of the actual relative smooth locus in that geometric fibre. -/
def smoothBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (smoothHc p ℓ n)

private def linearOfAddEquiv {E F : Type} [AddCommGroup E] [Module (ZMod ℓ) E]
    [AddCommGroup F] [Module (ZMod ℓ) F] (e : E ≃+ F) : E ≃ₗ[ZMod ℓ] F :=
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

/-- Compact cohomology of the actual proper geometric fibre agrees with ordinary model cohomology. -/
def properCohomologyEquiv (n : ℕ) : properHc p ℓ n ≃+ ordinaryH ℓ (projectiveNode (closureField p)) n := by
  let X := geometricFiber p
  let M := (constantSheaf X.smallEtaleTopology A).obj (coefficient ℓ)
  let e := ((Sheaf.functorH X.smallEtaleTopology n).mapIso
    ((extensionByZeroIdIso X).app M)).addCommGroupIsoToAddEquiv
  exact e.trans (schemeIsoCohomologyEquiv (projectiveIso p) (coefficient ℓ) n)

/-- Positive compact cohomology of the actual smooth locus agrees with the proper model. -/
def smoothPositiveCohomologyEquiv (n : ℕ) :
    smoothHc p ℓ (n + 1) ≃+ ordinaryH ℓ (projectiveNode (closureField p)) (n + 1) := by
  letI := origin_closed p
  exact (positiveEquiv (geometricSmoothOpen p).ι (closureField p) (origin p)
    (geometric_smooth_range p) (coefficient ℓ) n).trans
    (schemeIsoCohomologyEquiv (projectiveIso p) (coefficient ℓ) (n + 1))

theorem smoothHZero_subsingleton : Subsingleton (smoothHc p ℓ 0) := by
  letI := origin_closed p
  letI := geometric_preconnected p
  exact zero_subsingleton (geometricSmoothOpen p).ι (closureField p) (origin p)
    (geometric_smooth_range p) (coefficient ℓ)

private theorem properBetti_eq (n : ℕ) :
    properBetti p ℓ n = NodalSmoothEulerComparison.properCompactBetti (closureField p) ℓ n := by
  rw [NodalSmoothEulerComparison.proper_compact_betti_eq]
  letI := ordinaryModule ℓ (projectiveNode (closureField p)) n
  exact LinearEquiv.finrank_eq (linearOfAddEquiv ℓ (properCohomologyEquiv p ℓ n))

private theorem smoothBetti_eq (n : ℕ) :
    smoothBetti p ℓ n = NodalSmoothEulerComparison.smoothCompactBetti (closureField p) ℓ n := by
  cases n with
  | zero =>
    rw [NodalSmoothEulerComparison.smooth_betti_zero]
    letI := smoothHZero_subsingleton p ℓ
    exact Module.finrank_zero_of_subsingleton
  | succ n =>
    rw [NodalSmoothEulerComparison.smooth_betti_succ]
    letI := ordinaryModule ℓ (projectiveNode (closureField p)) (n + 1)
    exact LinearEquiv.finrank_eq (linearOfAddEquiv ℓ (smoothPositiveCohomologyEquiv p ℓ n))

private theorem two_ne_zero (hp : 2 < p) : (2 : closureField p) ≠ 0 := by
  intro h
  have hF := (algebraMap (ZMod p) (closureField p)).injective
    (show algebraMap (ZMod p) (closureField p) (2 : ZMod p) =
      algebraMap (ZMod p) (closureField p) 0 by simpa only [map_ofNat, map_zero] using h)
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using hF)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd)

variable [NeZero (ℓ : closureField p)]

/-- The actual proper geometric fibre has compact Euler characteristic one and its smooth open has zero. -/
theorem geometric_euler (hp : 2 < p) (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properBetti p ℓ n : ℤ)) = 1 ∧
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothBetti p ℓ n : ℤ)) = 0 := by
  simpa only [properBetti_eq, smoothBetti_eq] using
    NodalSmoothEulerComparison.complete_euler_comparison (closureField p) ℓ (two_ne_zero p hp) N hN

/-- On a single fixed integral nodal model, the arithmetic ordinary bump is zero at each odd prime,
the fibre is singular, and the geometric compact Euler characteristics are one and zero. -/
theorem arithmetic_bump_and_geometric_euler (hp : 2 < p) (N : ℕ) (hN : 3 ≤ N) :
    letI := IntegralOddPrimeBumps.binaryModule (IntegralOddPrimeFibers.nodalFiber p)
    letI := IntegralOddPrimeBumps.binaryModule (IntegralOddPrimeBumps.nodeSmooth p)
    (((Module.finrank (ZMod 2) (IntegralOddPrimeBumps.H (IntegralOddPrimeFibers.nodalFiber p)) : ℤ) -
        Module.finrank (ZMod 2) (IntegralOddPrimeBumps.H (IntegralOddPrimeBumps.nodeSmooth p)) = 0) ∧
      ¬ Smooth (IntegralOddPrimeFibers.nodeToResidue p)) ∧
    ((∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properBetti p ℓ n : ℤ)) = 1 ∧
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothBetti p ℓ n : ℤ)) = 0) :=
  ⟨IntegralOddPrimeBumps.node_zero_bump_and_nonsmooth p hp, geometric_euler p ℓ hp N hN⟩

end
end ManuscriptAudit.IntegralNodalGeometricEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalGeometricEuler.properCohomologyEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricEuler.smoothPositiveCohomologyEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricEuler.smoothHZero_subsingleton,
      ``ManuscriptAudit.IntegralNodalGeometricEuler.geometric_euler,
      ``ManuscriptAudit.IntegralNodalGeometricEuler.arithmetic_bump_and_geometric_euler] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
