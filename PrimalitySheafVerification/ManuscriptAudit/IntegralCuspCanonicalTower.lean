import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricReductions
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleTowerDifference

/-! All-degree canonical coefficient towers on the literal affine cusp and its actual smooth open. -/

namespace ManuscriptAudit.IntegralCuspCanonicalTower

open AlgebraicGeometry CategoryTheory
open IntegralCuspGeometricFiber (affineCompactOpen smoothCompactOpen)
open IntegralCuspGeometricPrimePower (affineHc smoothHc affinePrimePowerEquiv smoothPrimePowerEquiv)
open IntegralCuspGeometricReductions (affineReduction_two_surjective
  smoothReduction_one_surjective smoothReduction_two_surjective)
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCoefficientReduction (extendedConstants reductionH)
open OpenEtaleCyclicInverseLimit (compatibleClasses padicEquiv)
open OpenEtaleTowerDifference (difference_surjective compatibleClasses_subsingleton)

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private theorem orderOne_subsingleton {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Subsingleton (extensionH j (AddCommGrpCat.of (ZMod 1)) n) := by
  let F := extendedConstants j ⋙ Sheaf.functorH X.smallEtaleTopology n
  let M := AddCommGrpCat.of (ZMod 1)
  letI : Subsingleton M := inferInstanceAs (Subsingleton (ZMod 1))
  exact AddCommGrpCat.subsingleton_of_isZero (F.map_isZero (AddCommGrpCat.isZero_of_subsingleton M))

private def orderOneEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    extensionH j (AddCommGrpCat.of (ZMod 1)) n ≃+ ZMod 1 := by
  let h := orderOne_subsingleton j n
  exact AddEquiv.ofBijective (0 : extensionH j (AddCommGrpCat.of (ZMod 1)) n →+ ZMod 1)
    ⟨fun _ _ _ ↦ h.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩

private theorem trivial_of_equiv {B : Type} [AddCommGroup B] (e : B ≃+ ZMod 1) :
    Subsingleton B :=
  ⟨fun _ _ ↦ e.injective (Subsingleton.elim _ _)⟩

private theorem affine_level_vanish (hℓp : ℓ ≠ p) (n : ℕ) (hn : n ≠ 2) (r : ℕ) :
    Subsingleton (affineHc p (ℓ ^ r) n) := by
  cases r with
  | zero => exact orderOne_subsingleton (affineCompactOpen p) n
  | succ r => exact trivial_of_equiv ((affinePrimePowerEquiv p ℓ hℓp (r + 1) (by omega) n).trans
      (ZMod.ringEquivCongr (if_neg hn)).toAddEquiv)

private theorem smooth_level_vanish (hℓp : ℓ ≠ p) (n : ℕ) (hn : ¬ (n = 1 ∨ n = 2)) (r : ℕ) :
    Subsingleton (smoothHc p (ℓ ^ r) n) := by
  cases r with
  | zero => exact orderOne_subsingleton (smoothCompactOpen p) n
  | succ r => exact trivial_of_equiv ((smoothPrimePowerEquiv p ℓ hℓp (r + 1) (by omega) n).trans
      (ZMod.ringEquivCongr (if_neg hn)).toAddEquiv)

private theorem affine_onto (hℓp : ℓ ≠ p) (n r : ℕ) :
    Function.Surjective (reductionH (affineCompactOpen p) (ℓ ^ r) ℓ n) := by
  by_cases hn : n = 2
  · subst n
    exact affineReduction_two_surjective p ℓ hℓp r
  · exact fun x ↦ ⟨0, (affine_level_vanish p ℓ hℓp n hn r).elim _ x⟩

private theorem smooth_onto (hℓp : ℓ ≠ p) (n r : ℕ) :
    Function.Surjective (reductionH (smoothCompactOpen p) (ℓ ^ r) ℓ n) := by
  by_cases hn : n = 1 ∨ n = 2
  · rcases hn with rfl | rfl
    · cases r with
      | zero => exact fun x ↦ ⟨0, (orderOne_subsingleton (smoothCompactOpen p) 1).elim _ x⟩
      | succ r => exact smoothReduction_one_surjective p ℓ hℓp (r + 1) (by omega)
    · exact smoothReduction_two_surjective p ℓ hℓp r
  · exact fun x ↦ ⟨0, (smooth_level_vanish p ℓ hℓp n hn r).elim _ x⟩

/-- Both actual cusp product differences are onto in every compact degree. -/
theorem product_differences_onto (hℓp : ℓ ≠ p) (n : ℕ) :
    Function.Surjective (OpenEtaleTowerDifference.difference (affineCompactOpen p) ℓ n) ∧
      Function.Surjective (OpenEtaleTowerDifference.difference (smoothCompactOpen p) ℓ n) :=
  ⟨difference_surjective _ ℓ n (affine_onto p ℓ hℓp n),
    difference_surjective _ ℓ n (smooth_onto p ℓ hℓp n)⟩

/-- The canonical affine compatible classes in degree two are ℤℓ. -/
def affineLimitEquiv (hℓp : ℓ ≠ p) :
    compatibleClasses (affineCompactOpen p) ℓ 2 ≃+ ℤ_[ℓ] :=
  padicEquiv _ ℓ 2 (affine_onto p ℓ hℓp 2) (fun r ↦ by
    cases r with
    | zero => exact orderOneEquiv (affineCompactOpen p) 2
    | succ r => exact affinePrimePowerEquiv p ℓ hℓp (r + 1) (by omega) 2)

/-- The canonical smooth compatible classes in positive degrees one and two are ℤℓ. -/
def smoothLimitEquiv (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    compatibleClasses (smoothCompactOpen p) ℓ n ≃+ ℤ_[ℓ] := by
  let e (r : ℕ) : smoothHc p (ℓ ^ r) n ≃+ ZMod (ℓ ^ r) := by
    cases r with
    | zero => exact orderOneEquiv (smoothCompactOpen p) n
    | succ r => exact (smoothPrimePowerEquiv p ℓ hℓp (r + 1) (by omega) n).trans
        (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv
  exact padicEquiv (smoothCompactOpen p) ℓ n (smooth_onto p ℓ hℓp n) e

/-- The canonical cusp compatible classes vanish in all other nonnegative compact degrees. -/
theorem omittedLimits (hℓp : ℓ ≠ p) (n : ℕ) :
    (n ≠ 2 → Subsingleton (compatibleClasses (affineCompactOpen p) ℓ n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (compatibleClasses (smoothCompactOpen p) ℓ n)) :=
  ⟨fun h ↦ compatibleClasses_subsingleton _ ℓ n (affine_level_vanish p ℓ hℓp n h),
    fun h ↦ compatibleClasses_subsingleton _ ℓ n (smooth_level_vanish p ℓ hℓp n h)⟩

end
end ManuscriptAudit.IntegralCuspCanonicalTower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspCanonicalTower.product_differences_onto,
      ``ManuscriptAudit.IntegralCuspCanonicalTower.affineLimitEquiv,
      ``ManuscriptAudit.IntegralCuspCanonicalTower.smoothLimitEquiv,
      ``ManuscriptAudit.IntegralCuspCanonicalTower.omittedLimits] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
