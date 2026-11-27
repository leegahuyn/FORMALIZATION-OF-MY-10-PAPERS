import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Pi
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! Native torsion inverse limits as modules over the actual prime-adic integers. -/

namespace ManuscriptAudit.PowerTateModule

open TorsionFrobeniusModule PowerTorsionTower

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]

local instance levelPadicModule (n : ℕ) : Module ℤ_[l] (PowerTorsion l G n) :=
  Module.compHom (PowerTorsion l G n) (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n))

theorem compatible_residue (n : ℕ) (r : ℤ_[l]) :
    PadicResidueSystems.reduction l (Nat.le_succ n) (PadicInt.toZModPow (n + 1) r) =
      PadicInt.toZModPow n r :=
  RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) r

def compatiblePoints : Submodule ℤ_[l] (∀ n : ℕ, PowerTorsion l G n) where
  carrier := {x | ∀ n, transition l G n (x (n + 1)) = x n}
  zero_mem' := fun _ => map_zero _
  add_mem' := by
    intro x y hx hy n
    change transition l G n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro r x hx n
    change transition l G n (PadicInt.toZModPow (n + 1) r • x (n + 1)) =
      PadicInt.toZModPow n r • x n
    rw [transition_smul l G (Fact.out : Nat.Prime l).ne_zero, compatible_residue, hx n]

abbrev Tate := ↥(compatiblePoints l G)

def evaluate (n : ℕ) : Tate l G →ₗ[ℤ_[l]] PowerTorsion l G n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluate_smul (n : ℕ) (r : ℤ_[l]) (x : Tate l G) :
    evaluate l G n (r • x) = PadicInt.toZModPow n r • evaluate l G n x := rfl

theorem evaluate_transition (n : ℕ) (x : Tate l G) :
    transition l G n (evaluate l G (n + 1) x) = evaluate l G n x :=
  x.property n

@[ext] theorem ext {x y : Tate l G} (h : ∀ n, evaluate l G n x = evaluate l G n y) : x = y :=
  Subtype.ext (funext h)

variable {G} {H P : Type*} [AddCommGroup H] [AddCommGroup P]

def map (f : G →+ H) : Tate l G →ₗ[ℤ_[l]] Tate l H where
  toFun x := ⟨fun n => mapLinear (l ^ n) f (x.val n), fun n => by
    change transition l H n (mapAdd (l ^ (n + 1)) f (x.val (n + 1))) =
      mapAdd (l ^ n) f (x.val n)
    rw [map_transition, x.property n]⟩
  map_add' x y := ext l H fun n => map_add (mapLinear (l ^ n) f) (x.val n) (y.val n)
  map_smul' r x := ext l H fun n =>
    (mapLinear (l ^ n) f).map_smul (PadicInt.toZModPow n r) (x.val n)

@[simp] theorem evaluate_map (f : G →+ H) (n : ℕ) (x : Tate l G) :
    evaluate l H n (map l f x) = mapLinear (l ^ n) f (evaluate l G n x) := rfl

theorem map_injective (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (map l f) := by
  intro x y h
  apply ext l G
  intro n
  apply mapLinear_injective (l ^ n) f hf
  exact congrArg (evaluate l H n) h

def mapAddEquiv (e : G ≃+ H) : Tate l G ≃ₗ[ℤ_[l]] Tate l H :=
  LinearEquiv.ofBijective (map l e.toAddMonoidHom) ⟨map_injective l _ e.injective, by
    intro x
    refine ⟨map l e.symm.toAddMonoidHom x, ext l H fun n => ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply (evaluate l H n x : H)⟩

theorem map_comp (f : G →+ H) (g : H →+ P) :
    map l (g.comp f) = (map l g).comp (map l f) := by
  apply LinearMap.ext
  intro x
  apply ext l P
  intro n
  apply Subtype.ext
  rfl

def endMap : AddMonoid.End G →+* Module.End ℤ_[l] (Tate l G) where
  toFun f := map l f
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply ext l G
    intro n
    apply Subtype.ext
    rfl
  map_one' := by
    apply LinearMap.ext
    intro x
    apply ext l G
    intro n
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply ext l G
    intro n
    apply Subtype.ext
    rfl
  map_mul' f g := map_comp l g f

@[simp] theorem evaluate_endMap (f : AddMonoid.End G) (n : ℕ) (x : Tate l G) :
    evaluate l G n (endMap l f x) = mapLinear (l ^ n) f (evaluate l G n x) := rfl

end
end ManuscriptAudit.PowerTateModule

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateModule.compatible_residue,
      ``ManuscriptAudit.PowerTateModule.evaluate_smul,
      ``ManuscriptAudit.PowerTateModule.evaluate_transition,
      ``ManuscriptAudit.PowerTateModule.ext,
      ``ManuscriptAudit.PowerTateModule.evaluate_map,
      ``ManuscriptAudit.PowerTateModule.map_injective,
      ``ManuscriptAudit.PowerTateModule.mapAddEquiv,
      ``ManuscriptAudit.PowerTateModule.map_comp,
      ``ManuscriptAudit.PowerTateModule.evaluate_endMap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
