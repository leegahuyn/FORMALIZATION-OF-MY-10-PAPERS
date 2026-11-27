import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicSectionTower

/-! Simultaneous continuous lifts of all finite residues can be corrected
to a compatible system and hence to an actual continuous adic lift. -/

namespace ManuscriptAudit.PadicContinuousLiftFromResidues

open ProetalePadicSectionTower (sectionTransition compatibleSections continuousSectionsEquiv)
open CyclicPowerInverseLimit (reduction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩
local instance powNeZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩

private def split (n : ℕ) (a : ZMod (ℓ ^ n)) : ZMod (ℓ ^ (n + 1)) :=
  (a.val : ℕ)

private theorem split_zero (n : ℕ) : split ℓ n 0 = 0 := by simp [split]

private theorem reduction_split (n : ℕ) (a : ZMod (ℓ ^ n)) :
    reduction ℓ (Nat.le_succ n) (split ℓ n a) = a := by
  rw [split, map_natCast, ZMod.natCast_zmod_val]

variable {X : Type u} [TopologicalSpace X]

private def level (a : ∀ n, C(X, ZMod (ℓ ^ n))) : ∀ n, C(X, ZMod (ℓ ^ n))
  | 0 => 0
  | n + 1 => a (n + 1) +
      (⟨split ℓ n, continuous_of_discreteTopology⟩ : C(ZMod (ℓ ^ n), ZMod (ℓ ^ (n + 1)))).comp
        (level a n - sectionTransition ℓ X n (a (n + 1)))

private theorem level_compatible (a : ∀ n, C(X, ZMod (ℓ ^ n))) (n : ℕ) :
    sectionTransition ℓ X n (level ℓ a (n + 1)) = level ℓ a n := by
  apply ContinuousMap.ext
  intro x
  let ρ := reduction ℓ (Nat.le_succ n)
  change ρ (a (n + 1) x + split ℓ n (level ℓ a n x - ρ (a (n + 1) x))) = level ℓ a n x
  rw [map_add, show ρ (split ℓ n _) = _ from reduction_split ℓ n _,
    add_comm (ρ (a (n + 1) x)), sub_add_cancel]

variable {Y : Type v} [TopologicalSpace Y] (g : Y → X) (f : C(Y, ℤ_[ℓ]))
variable (a : ∀ n, C(X, ZMod (ℓ ^ n))) (h : ∀ n y, a n (g y) = PadicInt.toZModPow n (f y))

include h in
private theorem level_agrees (n : ℕ) (y : Y) :
    level ℓ a n (g y) = PadicInt.toZModPow n (f y) := by
  induction n with
  | zero =>
    change level ℓ a 0 (g y) = PadicInt.toZModPow 0 (f y)
    haveI : Subsingleton (ZMod (ℓ ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n ih =>
    let ρ := reduction ℓ (Nat.le_succ n)
    have hr : ρ (PadicInt.toZModPow (n + 1) (f y)) = PadicInt.toZModPow n (f y) :=
      RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) (f y)
    change a (n + 1) (g y) + split ℓ n (level ℓ a n (g y) - ρ (a (n + 1) (g y))) =
      PadicInt.toZModPow (n + 1) (f y)
    rw [h (n + 1) y, ih, hr, sub_self, split_zero, add_zero]

/-- Arbitrary simultaneous continuous residue lifts yield a continuous adic lift
of the displayed function along the same underlying map. -/
theorem exists_continuous_lift
    (hLift : ∀ n, ∃ a : C(X, ZMod (ℓ ^ n)), ∀ y, a (g y) = PadicInt.toZModPow n (f y)) :
    ∃ F : C(X, ℤ_[ℓ]), ∀ y, F (g y) = f y := by
  choose a h using hLift
  let b : compatibleSections ℓ X := ⟨level ℓ a, level_compatible ℓ a⟩
  let E := continuousSectionsEquiv ℓ X
  let F := E.symm b
  refine ⟨F, fun y ↦ PadicInt.ext_of_toZModPow.mp (fun n ↦ ?_)⟩
  have hE := congrArg (fun z : compatibleSections ℓ X ↦ z.val n (g y)) (E.apply_symm_apply b)
  change PadicInt.toZModPow n (F (g y)) = level ℓ a n (g y) at hE
  exact hE.trans (level_agrees ℓ g f a h n y)

end

end ManuscriptAudit.PadicContinuousLiftFromResidues

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PadicContinuousLiftFromResidues.exists_continuous_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
