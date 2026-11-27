import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricReductions

/-! Ordinary additive inverse limits of the actual geometric cusp compact cohomology groups. -/

namespace ManuscriptAudit.IntegralCuspGeometricInverseLimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralCuspGeometricFiber (affineCompactOpen smoothCompactOpen)
open IntegralCuspGeometricPrimePower (affineHc smoothHc affinePrimePowerEquiv smoothPrimePowerEquiv)
open IntegralCuspGeometricReductions
open OpenEtaleCoefficientReduction (extendedConstants)
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}

private theorem orderOne_subsingleton {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Subsingleton (extensionH j (AddCommGrpCat.of (ZMod 1)) n) := by
  let F := extendedConstants j ⋙ Sheaf.functorH X.smallEtaleTopology n
  let M := AddCommGrpCat.of (ZMod 1)
  letI : Subsingleton M := inferInstanceAs (Subsingleton (ZMod 1))
  exact AddCommGrpCat.subsingleton_of_isZero (F.map_isZero (AddCommGrpCat.isZero_of_subsingleton M))

private def orderOneEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    extensionH j (AddCommGrpCat.of (ZMod 1)) n ≃+ ZMod 1 := by
  letI := orderOne_subsingleton j n
  exact AddEquiv.ofBijective
    (0 : extensionH j (AddCommGrpCat.of (ZMod 1)) n →+ ZMod 1)
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev affineLevel (r : ℕ) := affineHc p (ℓ ^ r) 2
private abbrev smoothLevel (n r : ℕ) := smoothHc p (ℓ ^ r) n

private def coefficientCongr (G : ℕ → Type) [∀ d, AddCommGroup (G d)]
    {a b : ℕ} (h : a = b) : G a ≃+ G b := by
  subst b
  exact AddEquiv.refl _

private def affineTransition (r : ℕ) : affineLevel p ℓ (r + 1) →+ affineLevel p ℓ r :=
  (affineReduction p ℓ r 2).comp
    (coefficientCongr (fun d ↦ affineHc p d 2) (pow_succ ℓ r)).toAddMonoidHom

private def smoothTransition (n r : ℕ) : smoothLevel p ℓ n (r + 1) →+ smoothLevel p ℓ n r :=
  (smoothReduction p ℓ r n).comp
    (coefficientCongr (fun d ↦ smoothHc p d n) (pow_succ ℓ r)).toAddMonoidHom

private theorem affineTransition_surjective (hℓp : ℓ ≠ p) (r : ℕ) :
    Function.Surjective (affineTransition p ℓ r) :=
  (affineReduction_two_surjective p ℓ hℓp r).comp
    (coefficientCongr (fun d ↦ affineHc p d 2) (pow_succ ℓ r)).surjective

private def affineLevelEquiv (hℓp : ℓ ≠ p) (r : ℕ) : affineLevel p ℓ r ≃+ ZMod (ℓ ^ r) := by
  cases r with
  | zero => exact orderOneEquiv (affineCompactOpen p) 2
  | succ r => exact affinePrimePowerEquiv p ℓ hℓp (r + 1) (by omega) 2

private def smoothLevelEquiv (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) (r : ℕ) :
    smoothLevel p ℓ n r ≃+ ZMod (ℓ ^ r) := by
  cases r with
  | zero => exact orderOneEquiv (smoothCompactOpen p) n
  | succ r =>
    rcases hn with rfl | rfl
    · exact smoothPrimePowerEquiv p ℓ hℓp (r + 1) (by omega) 1
    · exact smoothPrimePowerEquiv p ℓ hℓp (r + 1) (by omega) 2

private theorem smoothTransition_surjective (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (r : ℕ) : Function.Surjective (smoothTransition p ℓ n r) := by
  rcases hn with rfl | rfl
  · cases r with
    | zero =>
      let h : Subsingleton (smoothLevel p ℓ 1 0) := orderOne_subsingleton (smoothCompactOpen p) 1
      exact fun x ↦ ⟨0, h.elim _ x⟩
    | succ r =>
      exact (smoothReduction_one_surjective p ℓ hℓp (r + 1) (by omega)).comp
        (coefficientCongr (fun d ↦ smoothHc p d 1) (pow_succ ℓ (r + 1))).surjective
  · exact (smoothReduction_two_surjective p ℓ hℓp r).comp
      (coefficientCongr (fun d ↦ smoothHc p d 2) (pow_succ ℓ r)).surjective

/-- Compatible tuples for the actual geometric cusp Hc² reduction maps. -/
def affineDegreeTwoLimit := CyclicPowerInverseLimit.compatibleTuples
  (affineLevel p ℓ) (affineTransition p ℓ)

/-- Compatible tuples for the actual smooth open in degree n. -/
def smoothDegreeLimit (n : ℕ) := CyclicPowerInverseLimit.compatibleTuples
  (smoothLevel p ℓ n) (smoothTransition p ℓ n)

/-- The ordinary inverse limit of the finite-level affine cusp Hc² groups is additively ℤℓ. -/
def affineDegreeTwoLimitEquiv (hℓp : ℓ ≠ p) : affineDegreeTwoLimit p ℓ ≃+ ℤ_[ℓ] :=
  CyclicPowerInverseLimit.padicEquiv ℓ (affineLevel p ℓ) (affineTransition p ℓ)
    (affineTransition_surjective p ℓ hℓp) (affineLevelEquiv p ℓ hℓp)

/-- The ordinary inverse limit of the smooth geometric Hc¹ or Hc² groups is additively ℤℓ. -/
def smoothDegreeLimitEquiv (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    smoothDegreeLimit p ℓ n ≃+ ℤ_[ℓ] :=
  CyclicPowerInverseLimit.padicEquiv ℓ (smoothLevel p ℓ n) (smoothTransition p ℓ n)
    (smoothTransition_surjective p ℓ hℓp n hn) (smoothLevelEquiv p ℓ hℓp n hn)

end
end ManuscriptAudit.IntegralCuspGeometricInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspGeometricInverseLimit.affineDegreeTwoLimitEquiv,
      ``ManuscriptAudit.IntegralCuspGeometricInverseLimit.smoothDegreeLimitEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
