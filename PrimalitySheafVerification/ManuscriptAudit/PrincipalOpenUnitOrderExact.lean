import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenDivisorNaturality

/-! Removing the rational point zero adds one independent integer order to the actual unit group. -/

namespace ManuscriptAudit.PrincipalOpenUnitOrderExact

open Polynomial
open AffineLineDivisor RatFuncPrincipalOpen

noncomputable section

variable (K : Type) [Field K]

abbrev removeZero (f : Polynomial K) := f * Polynomial.X

theorem removeZero_ne_zero (f : Polynomial K) (hf : f ≠ 0) :
    removeZero K f ≠ 0 :=
  mul_ne_zero hf Polynomial.X_ne_zero

private theorem open_le (f : Polynomial K) :
    PrimeSpectrum.basicOpen (removeZero K f) ≤ PrimeSpectrum.basicOpen f :=
  PrimeSpectrum.basicOpen_mul_le_left f Polynomial.X

/-- The actual ring restriction to the open obtained by removing zero. -/
def restriction (f : Polynomial K) :
    Additive (Localization.Away f)ˣ →+ Additive (Localization.Away (removeZero K f))ˣ :=
  restrictUnits K f (removeZero K f) (open_le K f)

/-- The order of an actual unit at the newly removed point. -/
def orderAtZero (f : Polynomial K) (hf : f ≠ 0) :
    Additive (Localization.Away (removeZero K f))ˣ →+ ℤ where
  toFun u := divisor K (unitMap K (removeZero K f) (removeZero_ne_zero K f hf) u) 0
  map_zero' := by simp only [map_zero, Finsupp.zero_apply]
  map_add' a b := by rw [map_add, map_add] <;> rfl

private theorem restrict_to_function_field (f : Polynomial K) (hf : f ≠ 0)
    (x : Additive (Localization.Away f)ˣ) :
    unitMap K (removeZero K f) (removeZero_ne_zero K f hf) (restriction K f x) =
      unitMap K f hf x :=
  DFunLike.congr_fun
    (unitMap_restrictUnits K f (removeZero K f) (open_le K f) hf (removeZero_ne_zero K f hf)) x

variable [IsAlgClosed K]

/-- Order zero characterizes exactly the units extending over the omitted point. -/
theorem restriction_order_exact (f : Polynomial K) (h0 : f.eval 0 ≠ 0) :
    Function.Exact (restriction K f) (orderAtZero K f (by
      intro hf
      apply h0
      rw [hf, Polynomial.eval_zero])) := by
  classical
  have hf : f ≠ 0 := by intro h; exact h0 (by rw [h, Polynomial.eval_zero])
  let g := removeZero K f
  let hg := removeZero_ne_zero K f hf
  intro u
  change divisor K (unitMap K g hg u) 0 = 0 ↔ ∃ x, restriction K f x = u
  constructor
  · intro hu
    let z := unitMap K g hg u
    have hG : divisorOnOpen K g z = 0 := (divisorOnOpen_exact K g hg z).mpr ⟨u, rfl⟩
    have hF : divisorOnOpen K f z = 0 := by
      apply Finsupp.ext
      intro a
      change divisor K z a.val = 0
      by_cases ha : a.val = 0
      · rw [ha]
        exact hu
      · have hga : g.eval a.val ≠ 0 := by
          change (f * Polynomial.X).eval a.val ≠ 0
          rw [Polynomial.eval_mul, Polynomial.eval_X]
          exact mul_ne_zero a.property ha
        exact congrArg (fun D : OpenPoint K g →₀ ℤ ↦ D ⟨a.val, hga⟩) hG
    obtain ⟨v, hv⟩ := (divisorOnOpen_exact K f hf z).mp hF
    refine ⟨v, (unitMap_injective K g hg) ?_⟩
    exact (restrict_to_function_field K f hf v).trans hv
  · rintro ⟨v, rfl⟩
    rw [restrict_to_function_field K f hf]
    have hF : divisorOnOpen K f (unitMap K f hf v) = 0 :=
      (divisorOnOpen_exact K f hf _).mpr ⟨v, rfl⟩
    exact congrArg (fun D : OpenPoint K f →₀ ℤ ↦ D ⟨0, h0⟩) hF

/-- Every integer is the order of an actual unit on the smaller principal open. -/
theorem orderAtZero_surjective (f : Polynomial K) (hf : f ≠ 0) :
    Function.Surjective (orderAtZero K f hf) := by
  classical
  intro n
  let g := removeZero K f
  let hg := removeZero_ne_zero K f hf
  obtain ⟨z, hz⟩ := divisor_surjective K (Finsupp.single 0 n)
  have hG : divisorOnOpen K g z = 0 := by
    apply Finsupp.ext
    intro a
    change divisor K z a.val = 0
    have ha : a.val ≠ 0 := by
      intro h
      apply a.property
      simp [g, removeZero, h]
    rw [hz]
    simp [Finsupp.single_apply, ha, Ne.symm ha]
  obtain ⟨u, hu⟩ := (divisorOnOpen_exact K g hg z).mp hG
  refine ⟨u, ?_⟩
  change divisor K (unitMap K g hg u) 0 = n
  rw [hu, hz, Finsupp.single_eq_same]

end
end ManuscriptAudit.PrincipalOpenUnitOrderExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PrincipalOpenUnitOrderExact.restriction_order_exact,
      ``ManuscriptAudit.PrincipalOpenUnitOrderExact.orderAtZero_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
