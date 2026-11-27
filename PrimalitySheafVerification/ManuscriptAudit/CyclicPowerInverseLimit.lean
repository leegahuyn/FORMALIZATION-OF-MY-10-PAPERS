import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerCoordinates

/-! Surjective cyclic prime-power towers have additive inverse limit isomorphic to the p-adic integers. -/

namespace ManuscriptAudit.CyclicPowerInverseLimit

universe u

noncomputable section

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
variable (transition : ∀ n, G (n + 1) →+ G n)
variable (onto : ∀ n, Function.Surjective (transition n))
variable (level : ∀ n, G n ≃+ ZMod (ℓ ^ n))

/-- Choose cyclic coordinates recursively so that every native transition is standard reduction. -/
def coordinates : ∀ n, G n ≃+ ZMod (ℓ ^ n)
  | 0 => level 0
  | n + 1 =>
    (CyclicPowerCoordinates.compatibleLift ℓ n (transition n) (onto n)
      (coordinates n) (level (n + 1))).1

theorem coordinates_reduction (n : ℕ) (x : G (n + 1)) :
    PadicResidueSystems.reduction ℓ (Nat.le_succ n) (coordinates ℓ G transition onto level (n + 1) x) =
      coordinates ℓ G transition onto level n (transition n x) :=
  (CyclicPowerCoordinates.compatibleLift ℓ n (transition n) (onto n)
    (coordinates ℓ G transition onto level n) (level (n + 1))).2 x

/-- The subgroup of compatible tuples, the ordinary inverse limit as an additive group. -/
def compatibleTuples : AddSubgroup (∀ n, G n) where
  carrier := {x | ∀ n, transition n (x (n + 1)) = x n}
  zero_mem' := fun n ↦ map_zero (transition n)
  add_mem' := by
    intro x y hx hy n
    change transition n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  neg_mem' := by
    intro x hx n
    change transition n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

/-- The componentwise coordinates identify compatible tuples with canonical residue systems. -/
def residueSystemsEquiv :
    compatibleTuples G transition ≃+ PadicResidueSystems.systems ℓ where
  toFun x := ⟨fun n ↦ coordinates ℓ G transition onto level n (x.val n),
    PadicResidueSystems.compatible_of_successors ℓ _ (fun n ↦ by
      rw [coordinates_reduction]
      exact congrArg (coordinates ℓ G transition onto level n) (x.property n))⟩
  invFun x := ⟨fun n ↦ (coordinates ℓ G transition onto level n).symm (x.val n),
    fun n ↦ by
      let en := coordinates ℓ G transition onto level n
      let es := coordinates ℓ G transition onto level (n + 1)
      change transition n (es.symm (x.val (n + 1))) = en.symm (x.val n)
      apply en.injective
      calc
        _ = PadicResidueSystems.reduction ℓ (Nat.le_succ n) (es (es.symm (x.val (n + 1)))) :=
          (coordinates_reduction ℓ G transition onto level n _).symm
        _ = x.val n := by rw [es.apply_symm_apply]; exact x.property n (n + 1) (Nat.le_succ n)
        _ = _ := (en.apply_symm_apply _).symm⟩
  left_inv x := Subtype.ext (funext fun n ↦ (coordinates ℓ G transition onto level n).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n ↦ (coordinates ℓ G transition onto level n).apply_symm_apply _)
  map_add' x y := Subtype.ext (funext fun n ↦ (coordinates ℓ G transition onto level n).map_add _ _)

/-- The ordinary additive inverse limit of the finite-level groups is the additive p-adic integers. -/
def padicEquiv : compatibleTuples G transition ≃+ ℤ_[ℓ] :=
  (residueSystemsEquiv ℓ G transition onto level).trans
    (PadicResidueSystems.padicRingEquiv ℓ).toAddEquiv.symm

/-- The equivalence preserves evaluation at each finite level through the coherent coordinates. -/
theorem padicEquiv_evaluation (n : ℕ) (x : compatibleTuples G transition) :
    PadicInt.toZModPow n (padicEquiv ℓ G transition onto level x) =
      coordinates ℓ G transition onto level n (x.val n) :=
  congrArg (PadicResidueSystems.evaluate ℓ n)
    ((PadicResidueSystems.padicRingEquiv ℓ).apply_symm_apply
      (residueSystemsEquiv ℓ G transition onto level x))

end
end ManuscriptAudit.CyclicPowerInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CyclicPowerInverseLimit.coordinates_reduction,
      ``ManuscriptAudit.CyclicPowerInverseLimit.residueSystemsEquiv,
      ``ManuscriptAudit.CyclicPowerInverseLimit.padicEquiv,
      ``ManuscriptAudit.CyclicPowerInverseLimit.padicEquiv_evaluation] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
