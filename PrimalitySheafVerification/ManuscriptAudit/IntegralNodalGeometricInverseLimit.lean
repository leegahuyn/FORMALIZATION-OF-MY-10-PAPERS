import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricPrimePower
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicReduction

/-! Ordinary compatible-tuple limits on the literal geometric fibres of the fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalGeometricInverseLimit

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open IntegralNodalGeometricPrimePower (affineCompactifyingOpen affineModelEquiv properModelEquiv
  smoothPositiveModelEquiv)
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveCyclicHOne (C)
open NodalCompactSupportHOne (nodalHcSuccProjectiveEquiv)
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCyclicInverseLimit (compatibleClasses padicEquiv)
open OpenEtaleCoefficientReduction (reductionH reductionH_surjective reductionH_surjective_of_next_cyclic)

noncomputable section

set_option backward.isDefEq.respectTransparency false
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

/-- Reduction is onto through degree two when the positive groups of the displayed
open compare with those of the actual proper geometric nodal model. -/
theorem reduction_onto {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (comparison : ∀ d n, extensionH j (M d) (n + 1) ≃+
      Sheaf.H (C (projectiveNode (closureField p)) d) (n + 1))
    (hp : 2 < p) (hℓp : ℓ ≠ p) (r n : ℕ) (hn : n ≤ 2) :
    Function.Surjective (reductionH j (ℓ ^ r) ℓ n) := by
  let K := closureField p
  let a := ℓ ^ r
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
  have hℓ : (ℓ : K) ≠ 0 := IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp
  have ha : (a : K) ≠ 0 := by
    change ((ℓ ^ r : ℕ) : K) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero r hℓ
  letI : NeZero (ℓ : K) := ⟨hℓ⟩
  letI : NeZero (a : K) := ⟨ha⟩
  letI : NeZero ((a * ℓ : ℕ) : K) := ⟨by rw [Nat.cast_mul]; exact mul_ne_zero ha hℓ⟩
  let e₃ : extensionH j (M ℓ) 3 ≃+ ZMod 1 :=
    (comparison ℓ 2).trans (NodalCompactSupportCyclicDegrees.ordinaryEquiv K ℓ h2 3)
  have h₃ : Subsingleton (extensionH j (M ℓ) 3) :=
    ⟨fun x y ↦ e₃.injective (Subsingleton.elim _ _)⟩
  have hR₂ := reductionH_surjective j a ℓ 2 h₃
  let e (d : ℕ) [NeZero (d : K)] (m : ℕ) (hm : m ≤ 1) :
      extensionH j (M d) (m + 1) ≃+ ZMod d :=
    (comparison d m).trans
      ((NodalCompactSupportCyclicDegrees.ordinaryEquiv K d h2 (m + 1)).trans
        (ZMod.ringEquivCongr (if_pos (by omega : m + 1 ≤ 2))).toAddEquiv)
  have hR₁ := reductionH_surjective_of_next_cyclic j a ℓ 1
    (e ℓ 1 (by decide)) (e (a * ℓ) 1 (by decide)) (e a 1 (by decide)) hR₂
  have hR₀ := reductionH_surjective_of_next_cyclic j a ℓ 0
    (e ℓ 0 (by decide)) (e (a * ℓ) 0 (by decide)) (e a 0 (by decide)) hR₁
  have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact hR₀
  · exact hR₁
  · exact hR₂

/-- Ordinary compact inverse-limit classes of the actual proper pullback. -/
abbrev properLimit (n : ℕ) := compatibleClasses (𝟙 (geometricFiber p)) ℓ n

/-- Ordinary compact inverse-limit classes of the actual affine chart. -/
abbrev affineLimit (n : ℕ) := compatibleClasses (affineCompactifyingOpen p) ℓ n

/-- Ordinary compact inverse-limit classes of the actual relative smooth open. -/
abbrev smoothLimit (n : ℕ) := compatibleClasses (geometricSmoothOpen p).ι ℓ n

/-- The actual proper geometric fibre has ordinary additive limit ℤℓ in degrees zero through two. -/
def properEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) (hn : n ≤ 2) : properLimit p ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (𝟙 (geometricFiber p)) ℓ n
    (fun r ↦ reduction_onto p ℓ (𝟙 (geometricFiber p)) (fun d k ↦ properModelEquiv p d (k + 1)) hp hℓp r n hn)
    (fun r ↦ (IntegralNodalGeometricPrimePower.properEquiv p ℓ hp hℓp r n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

/-- The actual affine geometric chart has ordinary additive limit ℤℓ in degrees one and two. -/
def affineEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    affineLimit p ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (affineCompactifyingOpen p) ℓ n
    (fun r ↦ reduction_onto p ℓ (affineCompactifyingOpen p)
      (fun d k ↦ (affineModelEquiv p d (k + 1)).trans
        (nodalHcSuccProjectiveEquiv (closureField p) (M d) k)) hp hℓp r n (by omega))
    (fun r ↦ (IntegralNodalGeometricPrimePower.affineEquiv p ℓ hp hℓp r n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

/-- The actual relative smooth geometric open has ordinary additive limit ℤℓ in degrees one and two. -/
def smoothEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    smoothLimit p ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv (geometricSmoothOpen p).ι ℓ n
    (fun r ↦ reduction_onto p ℓ (geometricSmoothOpen p).ι (smoothPositiveModelEquiv p) hp hℓp r n (by omega))
    (fun r ↦ (IntegralNodalGeometricPrimePower.smoothEquiv p ℓ hp hℓp r n).trans
      (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

end
end ManuscriptAudit.IntegralNodalGeometricInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalGeometricInverseLimit.reduction_onto,
      ``ManuscriptAudit.IntegralNodalGeometricInverseLimit.properEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricInverseLimit.affineEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricInverseLimit.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
