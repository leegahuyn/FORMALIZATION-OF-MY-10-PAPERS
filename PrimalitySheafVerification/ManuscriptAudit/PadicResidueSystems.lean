import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.RingHoms

/-! The compatible residue ring realized by the actual p-adic integers. -/

namespace ManuscriptAudit.PadicResidueSystems

noncomputable section

variable (p : ℕ)

def reduction {m n : ℕ} (h : m ≤ n) : ZMod (p ^ n) →+* ZMod (p ^ m) :=
  ZMod.castHom (pow_dvd_pow p h) _

theorem reduction_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (reduction p hab).comp (reduction p hbc) = reduction p (hab.trans hbc) :=
  RingHom.ext_zmod _ _

theorem reduction_refl (n : ℕ) : reduction p (le_refl n) = RingHom.id _ :=
  RingHom.ext_zmod _ _

def systems : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := {x | ∀ m n (h : m ≤ n), reduction p h (x n) = x m}
  zero_mem' := fun _ _ _ => map_zero _
  one_mem' := fun _ _ _ => map_one _
  add_mem' := by
    intro x y hx hy m n h
    change reduction p h (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  neg_mem' := by
    intro x hx m n h
    change reduction p h (-x n) = -x m
    rw [map_neg, hx m n h]
  mul_mem' := by
    intro x y hx hy m n h
    change reduction p h (x n * y n) = x m * y m
    rw [map_mul, hx m n h, hy m n h]

def evaluate (n : ℕ) : systems p →+* ZMod (p ^ n) where
  toFun x := x.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem evaluate_compatible (m n : ℕ) (h : m ≤ n) :
    (reduction p h).comp (evaluate p n) = evaluate p m :=
  RingHom.ext fun x => x.property m n h

theorem compatible_of_successors (x : ∀ n : ℕ, ZMod (p ^ n))
    (hx : ∀ n, reduction p (Nat.le_succ n) (x (n + 1)) = x n) :
    x ∈ systems p := by
  intro m n h
  induction h with
  | refl =>
    rw [reduction_refl]
    rfl
  | @step n h ih =>
    rw [← reduction_comp p h (Nat.le_succ n), RingHom.comp_apply, hx n, ih]

variable [Fact p.Prime]

def toSystems : ℤ_[p] →+* systems p where
  toFun x := ⟨fun n => PadicInt.toZModPow n x, fun m n h =>
    RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n h) x⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)

def padicRingEquiv : ℤ_[p] ≃+* systems p :=
  RingEquiv.ofBijective (toSystems p) ⟨by
    intro x y h
    exact PadicInt.ext_of_toZModPow.mp fun n =>
      congrArg (evaluate p n) h,
    by
    intro s
    refine ⟨PadicInt.lift (evaluate_compatible p) s, Subtype.ext (funext fun n => ?_)⟩
    exact RingHom.congr_fun (PadicInt.lift_spec (evaluate_compatible p) n) s⟩

@[simp] theorem evaluate_padicRingEquiv (n : ℕ) (x : ℤ_[p]) :
    evaluate p n (padicRingEquiv p x) = PadicInt.toZModPow n x := rfl

end
end ManuscriptAudit.PadicResidueSystems

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicResidueSystems.reduction_comp,
      ``ManuscriptAudit.PadicResidueSystems.reduction_refl,
      ``ManuscriptAudit.PadicResidueSystems.evaluate_compatible,
      ``ManuscriptAudit.PadicResidueSystems.compatible_of_successors,
      ``ManuscriptAudit.PadicResidueSystems.padicRingEquiv,
      ``ManuscriptAudit.PadicResidueSystems.evaluate_padicRingEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
