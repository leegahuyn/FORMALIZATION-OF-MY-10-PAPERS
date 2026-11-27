import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.SequentialInverseLimitDifference

/-! A coherent levelwise additive equivalence preserves compatible classes and product-difference surjectivity. -/

namespace ManuscriptAudit.CompatibleTowerCongruence

open CyclicPowerInverseLimit (compatibleTuples)
open SequentialInverseLimitDifference (productDifference)

noncomputable section

universe u v

variable (G : ℕ → Type u) (F : ℕ → Type v) [∀ r, AddCommGroup (G r)] [∀ r, AddCommGroup (F r)]
variable (t : ∀ r, G (r + 1) →+ G r) (s : ∀ r, F (r + 1) →+ F r)
variable (e : ∀ r, G r ≃+ F r) (h : ∀ r x, e r (t r x) = s r (e (r + 1) x))

/-- The product of the arbitrary levelwise additive isomorphisms. -/
def productEquiv : (∀ r, G r) ≃+ (∀ r, F r) where
  toFun x r := e r (x r)
  invFun y r := (e r).symm (y r)
  left_inv x := funext fun r ↦ (e r).symm_apply_apply (x r)
  right_inv y := funext fun r ↦ (e r).apply_symm_apply (y r)
  map_add' x y := funext fun r ↦ (e r).map_add (x r) (y r)

include h in
theorem productDifference_natural (x : ∀ r, G r) :
    productEquiv G F e (productDifference G t x) =
      productDifference F s (productEquiv G F e x) := by
  funext r
  change e r (x r - t r (x (r + 1))) = e r (x r) - s r (e (r + 1) (x (r + 1)))
  rw [map_sub, h]

/-- Product-difference surjectivity transfers to any coherently isomorphic tower. -/
include h in
theorem surjective_of_surjective
    (onto : Function.Surjective (productDifference F s)) :
    Function.Surjective (productDifference G t) := by
  intro y
  let E := productEquiv G F e
  obtain ⟨x, hx⟩ := onto (E y)
  refine ⟨E.symm x, E.injective ?_⟩
  rw [productDifference_natural G F t s e h]
  change productDifference F s (E (E.symm x)) = E y
  rw [E.apply_symm_apply]
  exact hx

/-- A coherent levelwise additive equivalence restricts to compatible classes. -/
def compatibleEquiv : compatibleTuples G t ≃+ compatibleTuples F s where
  toFun x := ⟨productEquiv G F e x.val, fun r ↦ (h r _).symm.trans (congrArg (e r) (x.property r))⟩
  invFun y := ⟨(productEquiv G F e).symm y.val, fun r ↦ by
    apply (e r).injective
    change e r (t r ((e (r + 1)).symm (y.val (r + 1)))) = e r ((e r).symm (y.val r))
    rw [h, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact y.property r⟩
  left_inv x := Subtype.ext ((productEquiv G F e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((productEquiv G F e).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((productEquiv G F e).map_add x.val y.val)

end
end ManuscriptAudit.CompatibleTowerCongruence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CompatibleTowerCongruence.productDifference_natural,
      ``ManuscriptAudit.CompatibleTowerCongruence.surjective_of_surjective,
      ``ManuscriptAudit.CompatibleTowerCongruence.compatibleEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
