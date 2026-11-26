import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Euler difference from a five-term exact sequence

For the compact-support localization of a curve and one rational point,
it remains to account for the boundary term in degrees zero and one.
The linear algebra here proves the signed formula from the actual maps
and their exactness.
-/

namespace ManuscriptAudit.FiveTermEuler

open Function Module

variable {K A B C D E : Type*} [Field K]
variable [AddCommGroup A] [Module K A] [FiniteDimensional K A]
variable [AddCommGroup B] [Module K B] [FiniteDimensional K B]
variable [AddCommGroup C] [Module K C] [FiniteDimensional K C]
variable [AddCommGroup D] [Module K D] [FiniteDimensional K D]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The signed Euler contribution of the middle term in
0 → A → B → C → D → E → 0. -/
theorem alternating_finrank
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D) (i : D →ₗ[K] E)
    (hf : Injective f) (hfg : Exact f g) (hgh : Exact g h)
    (hhi : Exact h i) (hi : Surjective i) :
    ((finrank K B : ℤ) - finrank K E) -
      ((finrank K A : ℤ) - finrank K D) = finrank K C := by
  have hB := g.finrank_range_add_finrank_ker
  have hC := h.finrank_range_add_finrank_ker
  have hD := i.finrank_range_add_finrank_ker
  rw [LinearMap.exact_iff.mp hfg, LinearMap.finrank_range_of_inj hf] at hB
  rw [LinearMap.exact_iff.mp hgh] at hC
  let e : (LinearMap.range i) ≃ₗ[K] E :=
    LinearEquiv.ofBijective (LinearMap.range i).subtype
      ⟨Subtype.val_injective, fun y => ⟨⟨y, LinearMap.mem_range.mpr (hi y)⟩, rfl⟩⟩
  rw [LinearMap.exact_iff.mp hhi, e.finrank_eq] at hD
  omega

end ManuscriptAudit.FiveTermEuler

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FiveTermEuler.alternating_finrank
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
