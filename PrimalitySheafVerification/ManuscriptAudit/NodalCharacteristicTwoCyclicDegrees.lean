import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoCompactSupport
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCoefficientReduction

/-! All finite invertible cyclic compact cohomology groups of the actual characteristic-two nodal equation. -/

namespace ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveCyclicHOne (C)
open NodalCharacteristicTwoProjective (projectiveIso)
open NodalSmoothLocus (nodePoint)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open NodalCompactSupportCyclicDegrees (properHc affineHc smoothHc properOrdinaryComparison)
open CuspCompactSupportSequence (cuspHc cuspHcSuccProjectiveEquiv)
open OpenComplementRationalPointCohomology (extensionH positiveEquiv zero_subsingleton)
open OpenEtaleCoefficientReduction (extendedConstants)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

private def trivialEquiv {B : Type} [AddCommGroup B] (h : Subsingleton B) : B ≃+ ZMod 1 :=
  AddEquiv.ofBijective (0 : B →+ ZMod 1)
    ⟨fun x y _ ↦ h.elim x y, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩

private def orderOneEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    extensionH j (M 1) n ≃+ ZMod 1 := by
  let F := extendedConstants j ⋙ Sheaf.functorH X.smallEtaleTopology n
  letI : Subsingleton (M 1) := inferInstanceAs (Subsingleton (ZMod 1))
  exact trivialEquiv (AddCommGrpCat.subsingleton_of_isZero (F.map_isZero (AddCommGrpCat.isZero_of_subsingleton (M 1))))

variable (K : Type) [Field K] [IsAlgClosed K] [CharP K 2]

/-- In positive degree the actual proper characteristic-two nodal cohomology computes affine cusp compact support. -/
def ordinaryPositiveComparison (d n : ℕ) :
    Sheaf.H (C (projectiveNode K) d) (n + 1) ≃+ cuspHc K (M d) (n + 1) :=
  (schemeIsoCohomologyEquiv (projectiveIso K) (M d) (n + 1)).trans
    (cuspHcSuccProjectiveEquiv K (M d) n).symm

/-- In the positive degrees the actual relative smooth open has the affine cusp compact groups. -/
def smoothPositiveComparison (d n : ℕ) :
    smoothHc K d (n + 1) ≃+ cuspHc K (M d) (n + 1) := by
  letI := projectiveOrigin_closed K
  exact (positiveEquiv (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (M d) n).trans
    (ordinaryPositiveComparison K d n)

variable (d : ℕ) [NeZero (d : K)]

private def cuspCyclicEquiv (n : ℕ) : cuspHc K (M d) n ≃+ ZMod (if n = 2 then d else 1) := by
  by_cases hd : 2 ≤ d
  · exact CuspCompactSupportCyclicDegrees.cuspEquiv K 2 d hd n
  · letI : NeZero d := NeZero.of_neZero_natCast K
    have h₀ := NeZero.ne d
    have h : d = 1 := by omega
    subst d
    exact (orderOneEquiv (CuspProperCompactification.affineOpen K) n).trans
      (ZMod.ringEquivCongr (by simp : 1 = (if n = 2 then 1 else 1))).toAddEquiv

private theorem positiveOrder (n : ℕ) :
    (if n + 1 = 2 then d else 1) = (if n + 1 = 0 ∨ n + 1 = 2 then d else 1) := by
  by_cases h : n + 1 = 2
  · rw [if_pos h, if_pos (Or.inr h)]
  · rw [if_neg h, if_neg (by omega : ¬ (n + 1 = 0 ∨ n + 1 = 2))]

/-- Ordinary proper cohomology of the characteristic-two fibre is cyclic exactly in degrees zero and two. -/
def ordinaryEquiv (n : ℕ) :
    Sheaf.H (C (projectiveNode K) d) n ≃+ ZMod (if n = 0 ∨ n = 2 then d else 1) := by
  cases n with
  | zero =>
    change Sheaf.H (C (projectiveNode K) d) 0 ≃+ ZMod d
    letI := NodalCompactSupportHZero.projectiveNode_irreducible K
    exact EtaleConstantHZero.constantHZeroEquiv (projectiveNode K) (M d) (nodePoint K)
  | succ n =>
    exact (ordinaryPositiveComparison K d n).trans
      ((cuspCyclicEquiv K d (n + 1)).trans (ZMod.ringEquivCongr (positiveOrder d n)).toAddEquiv)

/-- The actual proper model has one cyclic compact group in degrees zero and two. -/
def properEquiv (n : ℕ) : properHc K d n ≃+ ZMod (if n = 0 ∨ n = 2 then d else 1) :=
  (properOrdinaryComparison K d n).trans (ordinaryEquiv K d n)

/-- The actual affine nodal chart has one cyclic compact group, in degree two. -/
def affineEquiv (n : ℕ) : affineHc K d n ≃+ ZMod (if n = 2 then d else 1) := by
  cases n with
  | zero =>
    change affineHc K d 0 ≃+ ZMod 1
    exact trivialEquiv (NodalCompactSupportHZero.compact_HZero_subsingleton K (M d))
  | succ n =>
    exact (NodalCharacteristicTwoCompactSupport.affineHcSuccEquiv K (M d) n).trans
      (cuspCyclicEquiv K d (n + 1))

/-- The actual relative smooth open of the proper nodal model has one cyclic compact group, in degree two. -/
def smoothEquiv (n : ℕ) : smoothHc K d n ≃+ ZMod (if n = 2 then d else 1) := by
  cases n with
  | zero =>
    change smoothHc K d 0 ≃+ ZMod 1
    letI := projectiveOrigin_closed K
    letI := NodalCompactSupportHZero.projectiveNode_irreducible K
    exact trivialEquiv (zero_subsingleton (smoothOpen K).ι K (projectiveOrigin K) (smooth_range K) (M d))
  | succ n =>
    exact (smoothPositiveComparison K d n).trans (cuspCyclicEquiv K d (n + 1))

end
end ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.ordinaryPositiveComparison,
      ``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.smoothPositiveComparison,
      ``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.ordinaryEquiv,
      ``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.properEquiv,
      ``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.affineEquiv,
      ``ManuscriptAudit.NodalCharacteristicTwoCyclicDegrees.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
