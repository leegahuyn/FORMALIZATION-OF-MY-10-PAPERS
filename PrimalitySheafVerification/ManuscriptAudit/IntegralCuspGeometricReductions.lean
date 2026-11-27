import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFiniteAddGroups
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricPrimePower
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCoefficientReduction

/-! The genuine coefficient reduction maps on geometric cusp compact cohomology are surjective. -/

namespace ManuscriptAudit.IntegralCuspGeometricReductions

open CategoryTheory
open IntegralCuspGeometricFiber (affineCompactOpen smoothCompactOpen)
open IntegralCuspGeometricPrimePower
open IntegralNodalGeometricFiber (closureField)
open OpenEtaleCoefficientReduction (inclusionH reductionH reductionH_surjective
  inclusion_reduction_exact reductionH_surjective_of_next_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

/-- The actual map (H_c^n(X,\mathbf{Z}/\ell^{r+1})\to H_c^n(X,\mathbf{Z}/\ell^r)). -/
def affineReduction (r n : ℕ) :
    affineHc p (ℓ ^ r * ℓ) n →+ affineHc p (ℓ ^ r) n :=
  reductionH (affineCompactOpen p) (ℓ ^ r) ℓ n

/-- The same actual coefficient reduction on the relative smooth geometric open. -/
def smoothReduction (r n : ℕ) :
    smoothHc p (ℓ ^ r * ℓ) n →+ smoothHc p (ℓ ^ r) n :=
  reductionH (smoothCompactOpen p) (ℓ ^ r) ℓ n

private theorem affineHThree_subsingleton (hℓp : ℓ ≠ p) : Subsingleton (affineHc p ℓ 3) := by
  letI : NeZero (ℓ : closureField p) := ⟨by
    simpa only [pow_one] using primePower_ne_zero p ℓ hℓp 1⟩
  let e := affineModelEquiv p ℓ 3
  let h := CuspCompactSupportAllHigher.cuspHc_add_three_subsingleton (closureField p) p ℓ 0
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

private theorem smoothHThree_subsingleton (hℓp : ℓ ≠ p) : Subsingleton (smoothHc p ℓ 3) := by
  letI : NeZero (ℓ : closureField p) := ⟨by
    simpa only [pow_one] using primePower_ne_zero p ℓ hℓp 1⟩
  let e := smoothModelEquiv p ℓ 3
  let h := CuspCompactSupportAllHigher.punctureHc_add_three_subsingleton (closureField p) p ℓ 0
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

theorem affineReduction_two_surjective (hℓp : ℓ ≠ p) (r : ℕ) :
    Function.Surjective (affineReduction p ℓ r 2) :=
  reductionH_surjective (affineCompactOpen p) (ℓ ^ r) ℓ 2 (affineHThree_subsingleton p ℓ hℓp)

theorem smoothReduction_two_surjective (hℓp : ℓ ≠ p) (r : ℕ) :
    Function.Surjective (smoothReduction p ℓ r 2) :=
  reductionH_surjective (smoothCompactOpen p) (ℓ ^ r) ℓ 2 (smoothHThree_subsingleton p ℓ hℓp)

/-- In degree one the reduction on the smooth open is also onto.
The adjacent degree-two map is injective by exactness and the computed finite cardinalities. -/
theorem smoothReduction_one_surjective (hℓp : ℓ ≠ p) (r : ℕ) (hr : 1 ≤ r) :
    Function.Surjective (smoothReduction p ℓ r 1) := by
  let a := ℓ ^ r
  let j := smoothCompactOpen p
  let i := inclusionH j a ℓ 2
  let g := reductionH j a ℓ 2
  have hℓ : (ℓ : closureField p) ≠ 0 := by
    simpa only [pow_one] using primePower_ne_zero p ℓ hℓp 1
  have ha : (a : closureField p) ≠ 0 := primePower_ne_zero p ℓ hℓp r
  letI : NeZero (ℓ : closureField p) := ⟨hℓ⟩
  letI : NeZero ((a * ℓ : ℕ) : closureField p) := ⟨by
    rw [Nat.cast_mul]
    exact mul_ne_zero ha hℓ⟩
  have hPrime : ℓ.Prime := Fact.out
  have haPos : 1 ≤ a := pow_pos hPrime.pos r
  have hTwo : 2 ≤ a * ℓ :=
    hPrime.two_le.trans ((one_mul ℓ).symm.trans_le (Nat.mul_le_mul_right ℓ haPos))
  let eA := (smoothModelEquiv p ℓ 2).trans
    (CuspCompactSupportCyclicDegrees.punctureTwoEquiv (closureField p) p ℓ hPrime.two_le)
  let eB := (smoothModelEquiv p (a * ℓ) 2).trans
    (CuspCompactSupportCyclicDegrees.punctureTwoEquiv (closureField p) p (a * ℓ) hTwo)
  let eC : smoothHc p a 2 ≃+ ZMod a := smoothPrimePowerEquiv p ℓ hℓp r hr 2
  letI : NeZero a := inferInstanceAs (NeZero (ℓ ^ r))
  letI : NeZero (a * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne ℓ)⟩
  letI : Finite (smoothHc p ℓ 2) := Finite.of_injective eA eA.injective
  letI : Finite (smoothHc p (a * ℓ) 2) := Finite.of_injective eB eB.injective
  letI : Finite (smoothHc p a 2) := Finite.of_injective eC eC.injective
  have hCard : Nat.card (smoothHc p (a * ℓ) 2) =
      Nat.card (smoothHc p a 2) * Nat.card (smoothHc p ℓ 2) := by
    simp only [Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv, Nat.card_congr eC.toEquiv, Nat.card_zmod]
  have hg : Function.Surjective g := smoothReduction_two_surjective p ℓ hℓp r
  have hi : Function.Injective i :=
    ExactFiniteAddGroups.first_injective i g (inclusion_reduction_exact j a ℓ 2) hg hCard
  exact reductionH_surjective_of_next_injective j a ℓ 1 hi

end
end ManuscriptAudit.IntegralCuspGeometricReductions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspGeometricReductions.affineReduction_two_surjective,
      ``ManuscriptAudit.IntegralCuspGeometricReductions.smoothReduction_two_surjective,
      ``ManuscriptAudit.IntegralCuspGeometricReductions.smoothReduction_one_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
