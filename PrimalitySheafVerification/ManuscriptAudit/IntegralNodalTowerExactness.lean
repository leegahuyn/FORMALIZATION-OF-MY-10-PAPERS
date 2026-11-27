import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleTowerDifference

/-! Exactness of the sequential product difference for the actual integral nodal cohomology towers. -/

namespace ManuscriptAudit.IntegralNodalTowerExactness

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open IntegralNodalGeometricPrimePower (affineCompactifyingOpen properModelEquiv affineModelEquiv
  smoothPositiveModelEquiv)
open IntegralNodalGeometricInverseLimit (properLimit affineLimit smoothLimit reduction_onto)
open IntegralNodalCharacteristicTwoInverseLimit (proper_reduction_onto affine_reduction_onto
  smooth_reduction_onto)
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveCyclicHOne (C)
open NodalCompactSupportHOne (nodalHcSuccProjectiveEquiv)
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCoefficientReduction (reductionH)
open OpenEtaleTowerDifference (difference difference_surjective compatibleClasses_subsingleton)

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

private theorem level_subsingleton {B : Type} [AddCommGroup B] {d : ℕ}
    {q : Prop} [Decidable q] (e : B ≃+ ZMod (if q then d else 1)) (h : ¬ q) :
    Subsingleton B :=
  let e' := e.trans (ZMod.ringEquivCongr (if_neg h)).toAddEquiv
  ⟨fun x y ↦ e'.injective (Subsingleton.elim _ _)⟩

private theorem onto_subsingleton {B D : Type} [Zero B] {f : B → D}
    (h : Subsingleton D) : Function.Surjective f :=
  fun y ↦ ⟨0, h.elim (f 0) y⟩

/-- At (2), the product differences of the literal proper, affine, and smooth
compact cohomology towers are surjective in every degree. -/
theorem difference_at_two (hℓ₂ : ℓ ≠ 2) (n : ℕ) :
    Function.Surjective (difference (𝟙 (geometricFiber 2)) ℓ n) ∧
      Function.Surjective (difference (affineCompactifyingOpen 2) ℓ n) ∧
      Function.Surjective (difference (geometricSmoothOpen 2).ι ℓ n) := by
  letI : NeZero (ℓ : closureField 2) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  refine ⟨difference_surjective _ ℓ n ?_, difference_surjective _ ℓ n ?_,
    difference_surjective _ ℓ n ?_⟩
  · intro r
    by_cases hn : n = 0 ∨ n = 2
    · exact proper_reduction_onto ℓ hℓ₂ r n hn
    · exact onto_subsingleton
        (level_subsingleton (IntegralNodalCharacteristicTwoCohomology.properEquiv ℓ n) hn)
  · intro r
    by_cases hn : n = 2
    · subst n
      exact affine_reduction_onto ℓ hℓ₂ r
    · exact onto_subsingleton
        (level_subsingleton (IntegralNodalCharacteristicTwoCohomology.affineEquiv ℓ n) hn)
  · intro r
    by_cases hn : n = 2
    · subst n
      exact smooth_reduction_onto ℓ hℓ₂ r
    · exact onto_subsingleton
        (level_subsingleton (IntegralNodalCharacteristicTwoCohomology.smoothEquiv ℓ n) hn)

/-- The actual characteristic-two compatible-class limits vanish outside their displayed degrees. -/
theorem limits_at_two_vanish (hℓ₂ : ℓ ≠ 2) (n : ℕ) :
    (¬ (n = 0 ∨ n = 2) → Subsingleton (properLimit 2 ℓ n)) ∧
      (n ≠ 2 → Subsingleton (affineLimit 2 ℓ n)) ∧
      (n ≠ 2 → Subsingleton (smoothLimit 2 ℓ n)) := by
  refine ⟨fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_,
    fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_,
    fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_⟩
  · exact fun r ↦ level_subsingleton
      (IntegralNodalCharacteristicTwoCohomology.properPrimePowerEquiv ℓ hℓ₂ r n) h
  · exact fun r ↦ level_subsingleton
      (IntegralNodalCharacteristicTwoCohomology.affinePrimePowerEquiv ℓ hℓ₂ r n) h
  · exact fun r ↦ level_subsingleton
      (IntegralNodalCharacteristicTwoCohomology.smoothPrimePowerEquiv ℓ hℓ₂ r n) h

private theorem odd_reduction_onto (p : ℕ) [Fact p.Prime]
    {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (comparison : ∀ d n, extensionH j (M d) (n + 1) ≃+
      Sheaf.H (C (projectiveNode (closureField p)) d) (n + 1))
    (hp : 2 < p) (hℓp : ℓ ≠ p) (r n : ℕ) :
    Function.Surjective (reductionH j (ℓ ^ r) ℓ n) := by
  by_cases hn : n ≤ 2
  · exact reduction_onto p ℓ j comparison hp hℓp r n hn
  · cases n with
    | zero => exact (hn (by decide)).elim
    | succ n =>
      letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp⟩
      have h2 : (2 : closureField p) ≠ 0 :=
        IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
      let e := (comparison ℓ n).trans
        (NodalCompactSupportCyclicDegrees.ordinaryEquiv (closureField p) ℓ h2 (n + 1))
      exact onto_subsingleton (level_subsingleton e hn)

/-- At every odd residue prime, the product differences of the three literal
compact cohomology towers are also surjective in every degree. -/
theorem difference_at_odd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) :
    Function.Surjective (difference (𝟙 (geometricFiber p)) ℓ n) ∧
      Function.Surjective (difference (affineCompactifyingOpen p) ℓ n) ∧
      Function.Surjective (difference (geometricSmoothOpen p).ι ℓ n) := by
  refine ⟨difference_surjective _ ℓ n ?_, difference_surjective _ ℓ n ?_,
    difference_surjective _ ℓ n ?_⟩
  · exact fun r ↦ odd_reduction_onto ℓ p (𝟙 (geometricFiber p))
      (fun d k ↦ properModelEquiv p d (k + 1)) hp hℓp r n
  · exact fun r ↦ odd_reduction_onto ℓ p (affineCompactifyingOpen p)
      (fun d k ↦ (affineModelEquiv p d (k + 1)).trans
        (nodalHcSuccProjectiveEquiv (closureField p) (M d) k)) hp hℓp r n
  · exact fun r ↦ odd_reduction_onto ℓ p (geometricSmoothOpen p).ι
      (smoothPositiveModelEquiv p) hp hℓp r n

/-- The actual odd-characteristic compatible-class limits vanish outside their displayed degrees. -/
theorem limits_at_odd_vanish (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) :
    (¬ n ≤ 2 → Subsingleton (properLimit p ℓ n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (affineLimit p ℓ n)) ∧
      (¬ (n = 1 ∨ n = 2) → Subsingleton (smoothLimit p ℓ n)) := by
  refine ⟨fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_,
    fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_,
    fun h ↦ compatibleClasses_subsingleton _ ℓ n ?_⟩
  · exact fun r ↦ level_subsingleton
      (IntegralNodalGeometricPrimePower.properEquiv p ℓ hp hℓp r n) h
  · exact fun r ↦ level_subsingleton
      (IntegralNodalGeometricPrimePower.affineEquiv p ℓ hp hℓp r n) h
  · exact fun r ↦ level_subsingleton
      (IntegralNodalGeometricPrimePower.smoothEquiv p ℓ hp hℓp r n) h

end
end ManuscriptAudit.IntegralNodalTowerExactness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalTowerExactness.difference_at_two,
      ``ManuscriptAudit.IntegralNodalTowerExactness.limits_at_two_vanish,
      ``ManuscriptAudit.IntegralNodalTowerExactness.difference_at_odd,
      ``ManuscriptAudit.IntegralNodalTowerExactness.limits_at_odd_vanish] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
