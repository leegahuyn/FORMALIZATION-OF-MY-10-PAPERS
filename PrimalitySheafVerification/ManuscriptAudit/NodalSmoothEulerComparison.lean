import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.NodalFiniteCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.OpenComplementRationalPointCohomology

/-! The proper node and its actual smooth open have equal ordinary H¹ dimensions but distinct compact Euler sums. -/

namespace ManuscriptAudit.NodalSmoothEulerComparison

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalSmoothLocus (nodePoint)
open NodalSmoothLocusOverlap (smoothOpen smoothScheme)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open NodalCompactSupportScalar (coefficient compactModule ordinaryModule extensionModule)
open NodalCompactSupportHOne (nodalHcSuccProjectiveEquiv)
open OpenEtaleExtension (extensionByZeroIdIso)
open OpenComplementRationalPointCohomology (extensionH positiveEquiv zero_subsingleton)
open scoped BigOperators

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt compactModule

variable (K : Type) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{0}
private abbrev properH (n : ℕ) :=
  Sheaf.H ((constantSheaf (projectiveNode K).smallEtaleTopology A).obj (coefficient ℓ)) n
private abbrev smoothH (n : ℕ) :=
  Sheaf.H ((constantSheaf (smoothScheme K).smallEtaleTopology A).obj (coefficient ℓ)) n
private abbrev smoothHc (n : ℕ) := extensionH (smoothOpen K).ι (coefficient ℓ) n
private abbrev properHc (n : ℕ) := extensionH (𝟙 (projectiveNode K)) (coefficient ℓ) n

private def properModule (n : ℕ) : Module (ZMod ℓ) (properH K ℓ n) :=
  ordinaryModule ℓ (projectiveNode K) n
private def smoothOrdinaryModule (n : ℕ) : Module (ZMod ℓ) (smoothH K ℓ n) :=
  ordinaryModule ℓ (smoothScheme K) n
private def smoothCompactModule (n : ℕ) : Module (ZMod ℓ) (smoothHc K ℓ n) :=
  extensionModule ℓ (smoothOpen K).ι n

private def properCompactModule (n : ℕ) : Module (ZMod ℓ) (properHc K ℓ n) :=
  extensionModule ℓ (𝟙 (projectiveNode K)) n

attribute [local instance] properModule smoothOrdinaryModule smoothCompactModule properCompactModule

/-- Ordinary Betti dimensions of the genuine proper model, which is compact. -/
def properBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (properH K ℓ n)

/-- Compact Betti dimensions on the actual proper model using the identity compactification. -/
def properCompactBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (properHc K ℓ n)

/-- Compact Betti dimensions of its genuine smooth open. -/
def smoothCompactBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (smoothHc K ℓ n)

/-- Ordinary Betti dimensions of its genuine smooth open. -/
def smoothOrdinaryBetti (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (smoothH K ℓ n)

private def linearOfAddEquiv {E F : Type} [AddCommGroup E] [Module (ZMod ℓ) E]
    [AddCommGroup F] [Module (ZMod ℓ) F] (e : E ≃+ F) : E ≃ₗ[ZMod ℓ] F :=
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

/-- On the actual proper scheme, identity extension gives the same Betti dimensions. -/
theorem proper_compact_betti_eq (n : ℕ) : properCompactBetti K ℓ n = properBetti K ℓ n := by
  let X := projectiveNode K
  let M := (constantSheaf X.smallEtaleTopology A).obj (coefficient ℓ)
  let e := ((Sheaf.functorH X.smallEtaleTopology n).mapIso
    ((extensionByZeroIdIso X).app M)).addCommGroupIsoToAddEquiv
  exact LinearEquiv.finrank_eq (linearOfAddEquiv ℓ e)

theorem proper_betti_zero : properBetti K ℓ 0 = 1 := by
  letI := NodalCompactSupportHZero.projectiveNode_irreducible K
  let e := EtaleConstantHZero.constantHZeroEquiv (projectiveNode K) (coefficient ℓ) (nodePoint K)
  exact (LinearEquiv.finrank_eq (linearOfAddEquiv ℓ e)).trans (Module.finrank_self _)

theorem smooth_betti_zero : smoothCompactBetti K ℓ 0 = 0 := by
  letI := NodalCompactSupportHZero.projectiveNode_irreducible K
  letI := projectiveOrigin_closed K
  letI := zero_subsingleton (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (coefficient ℓ)
  exact Module.finrank_zero_of_subsingleton

theorem proper_betti_succ (n : ℕ) :
    properBetti K ℓ (n + 1) = NodalFiniteCohomology.betti K ℓ (n + 1) :=
  LinearEquiv.finrank_eq (linearOfAddEquiv ℓ (nodalHcSuccProjectiveEquiv K (coefficient ℓ) n).symm)

theorem smooth_betti_succ (n : ℕ) :
    smoothCompactBetti K ℓ (n + 1) = properBetti K ℓ (n + 1) := by
  letI := projectiveOrigin_closed K
  let e := positiveEquiv (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (coefficient ℓ) n
  exact LinearEquiv.finrank_eq (linearOfAddEquiv ℓ e)

private theorem smooth_betti_eq_affine_compact (n : ℕ) :
    smoothCompactBetti K ℓ n = NodalFiniteCohomology.betti K ℓ n := by
  cases n with
  | zero => rw [smooth_betti_zero, NodalFiniteCohomology.betti_zero]
  | succ n => exact (smooth_betti_succ K ℓ n).trans (proper_betti_succ K ℓ n)

variable [NeZero (ℓ : K)]

/-- The proper model and its smooth open both have literal ordinary first Betti dimension one. -/
theorem ordinary_first_betti (h2 : (2 : K) ≠ 0) :
    properBetti K ℓ 1 = 1 ∧ smoothOrdinaryBetti K ℓ 1 = 1 := by
  refine ⟨(proper_betti_succ K ℓ 0).trans (NodalFiniteCohomology.betti_one K ℓ h2), ?_⟩
  let e := (NodalSmoothLocusCohomology.smoothLocusCyclicHOneEquiv K h2 ℓ
    (Fact.out : ℓ.Prime).two_le).symm
  exact (LinearEquiv.finrank_eq (linearOfAddEquiv ℓ e)).trans (Module.finrank_self _)

/-- The true compact Euler sums are one for the proper model and zero for its actual smooth open. -/
theorem complete_euler_comparison (h2 : (2 : K) ≠ 0) (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properCompactBetti K ℓ n : ℤ)) = 1 ∧
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothCompactBetti K ℓ n : ℤ)) = 0 := by
  have hs : (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothCompactBetti K ℓ n : ℤ)) = 0 := by
    simpa only [smooth_betti_eq_affine_compact K ℓ] using
      NodalFiniteCohomology.complete_compact_euler K ℓ h2 N hN
  have hDiff : (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properBetti K ℓ n : ℤ)) =
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothCompactBetti K ℓ n : ℤ)) + 1 := by
    cases N with
    | zero => omega
    | succ N =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ', proper_betti_zero, smooth_betti_zero]
      simp only [pow_zero, Nat.cast_one, Nat.cast_zero, one_mul, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [smooth_betti_succ]
  have hProper : (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properBetti K ℓ n : ℤ)) = 1 :=
    hDiff.trans (by rw [hs, zero_add])
  exact ⟨by simpa only [proper_compact_betti_eq K ℓ] using hProper, hs⟩

/-- The actual ordinary signed first Betti difference and the actual compact Euler difference disagree. -/
theorem ordinary_difference_ne_compact_euler (h2 : (2 : K) ≠ 0) (N : ℕ) (hN : 3 ≤ N) :
    ((properBetti K ℓ 1 : ℤ) - (smoothOrdinaryBetti K ℓ 1 : ℤ)) ≠
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (properCompactBetti K ℓ n : ℤ)) -
        (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (smoothCompactBetti K ℓ n : ℤ)) := by
  obtain ⟨hp, hs⟩ := ordinary_first_betti K ℓ h2
  obtain ⟨heP, heS⟩ := complete_euler_comparison K ℓ h2 N hN
  norm_num [hp, hs, heP, heS]

end
end ManuscriptAudit.NodalSmoothEulerComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothEulerComparison.proper_compact_betti_eq,
      ``ManuscriptAudit.NodalSmoothEulerComparison.ordinary_first_betti,
      ``ManuscriptAudit.NodalSmoothEulerComparison.complete_euler_comparison,
      ``ManuscriptAudit.NodalSmoothEulerComparison.ordinary_difference_ne_compact_euler] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
