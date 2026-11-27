import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Pi
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionReduction

/-! The actual 2-adic Tate module of an abelian group, with native torsion projections. -/

namespace ManuscriptAudit.TwoPowerTateModule

open TorsionFrobeniusModule TwoPowerTorsionTower

noncomputable section

variable (G : Type*) [AddCommGroup G]

local instance levelPadicModule (n : ℕ) : Module ℤ_[2] (PowerTorsion G n) :=
  Module.compHom (PowerTorsion G n) (PadicInt.toZModPow n : ℤ_[2] →+* ZMod (2 ^ n))

theorem compatible_residue (n : ℕ) (r : ℤ_[2]) :
    TwoPowerTorsionReduction.reduction n (PadicInt.toZModPow (n + 1) r) =
      PadicInt.toZModPow n r := by
  have e : TwoPowerTorsionReduction.reduction n =
      PadicResidueSystems.reduction 2 (Nat.le_succ n) := RingHom.ext_zmod _ _
  rw [e]
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) r

def compatiblePoints : Submodule ℤ_[2] (∀ n : ℕ, PowerTorsion G n) where
  carrier := {x | ∀ n, transition G n (x (n + 1)) = x n}
  zero_mem' := fun _ => map_zero _
  add_mem' := by
    intro x y hx hy n
    change transition G n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro r x hx n
    change transition G n (PadicInt.toZModPow (n + 1) r • x (n + 1)) =
      PadicInt.toZModPow n r • x n
    rw [TwoPowerTorsionReduction.transition_smul, compatible_residue, hx n]

abbrev Tate := ↥(compatiblePoints G)

def evaluate (n : ℕ) : Tate G →ₗ[ℤ_[2]] PowerTorsion G n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluate_smul (n : ℕ) (r : ℤ_[2]) (x : Tate G) :
    evaluate G n (r • x) = PadicInt.toZModPow n r • evaluate G n x := rfl

theorem evaluate_transition (n : ℕ) (x : Tate G) :
    transition G n (evaluate G (n + 1) x) = evaluate G n x :=
  x.property n

@[ext] theorem ext {x y : Tate G} (h : ∀ n, evaluate G n x = evaluate G n y) : x = y :=
  Subtype.ext (funext h)

variable {G} {H : Type*} [AddCommGroup H]

def map (f : G →+ H) : Tate G →ₗ[ℤ_[2]] Tate H where
  toFun x := ⟨fun n => mapLinear (2 ^ n) f (x.val n), fun n => by
    change transition H n (mapAdd (2 ^ (n + 1)) f (x.val (n + 1))) =
      mapAdd (2 ^ n) f (x.val n)
    rw [map_transition, x.property n]⟩
  map_add' x y := ext H fun n => map_add (mapLinear (2 ^ n) f) (x.val n) (y.val n)
  map_smul' r x := ext H fun n =>
    (mapLinear (2 ^ n) f).map_smul (PadicInt.toZModPow n r) (x.val n)

@[simp] theorem evaluate_map (f : G →+ H) (n : ℕ) (x : Tate G) :
    evaluate H n (map f x) = mapLinear (2 ^ n) f (evaluate G n x) := rfl

theorem map_injective (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro x y h
  apply ext G
  intro n
  apply mapLinear_injective (2 ^ n) f hf
  exact congrArg (evaluate H n) h

end
end ManuscriptAudit.TwoPowerTateModule

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTateModule.compatible_residue,
      ``ManuscriptAudit.TwoPowerTateModule.evaluate_smul,
      ``ManuscriptAudit.TwoPowerTateModule.evaluate_transition,
      ``ManuscriptAudit.TwoPowerTateModule.ext,
      ``ManuscriptAudit.TwoPowerTateModule.evaluate_map,
      ``ManuscriptAudit.TwoPowerTateModule.map_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
