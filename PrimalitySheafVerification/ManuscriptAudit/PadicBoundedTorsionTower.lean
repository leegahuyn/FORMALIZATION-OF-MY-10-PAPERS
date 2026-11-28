import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Compatible additive groups killed by successive prime powers inherit
their native scalar action from the corresponding p-adic residues. -/

namespace ManuscriptAudit.PadicBoundedTorsionTower

open PowerTateModule

noncomputable section

universe u v
variable (l : ℕ) [Fact l.Prime]
variable (A : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module (ZMod (l ^ n)) (A n)]

local instance levelModule (n : ℕ) : Module ℤ_[l] (A n) :=
  Module.compHom (A n) (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n))

variable (f : ∀ n, A (n + 1) →+ A n)

private theorem step_smul (n : ℕ) (r : ZMod (l ^ (n + 1))) (a : A (n + 1)) :
    f n (r • a) = PadicResidueSystems.reduction l (Nat.le_succ n) r • f n a := by
  letI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hS : r • a = r.val • a := by
    calc
      _ = (r.val : ZMod (l ^ (n + 1))) • a :=
        congrArg (fun q : ZMod (l ^ (n + 1)) => q • a) (ZMod.natCast_zmod_val r).symm
      _ = _ := Nat.cast_smul_eq_nsmul _ _
  have hR : PadicResidueSystems.reduction l (Nat.le_succ n) r = (r.val : ZMod (l ^ n)) := by
    calc
      _ = PadicResidueSystems.reduction l (Nat.le_succ n) (r.val : ZMod (l ^ (n + 1))) :=
        congrArg (PadicResidueSystems.reduction l (Nat.le_succ n)) (ZMod.natCast_zmod_val r).symm
      _ = _ := map_natCast _ _
  rw [hS, hR, Nat.cast_smul_eq_nsmul, map_nsmul]

/-- The actual compatible tuples form a module for the p-adic integers
via the corresponding finite residue at each coordinate. -/
def compatible : Submodule ℤ_[l] (∀ n, A n) where
  carrier := {x | ∀ n, f n (x (n + 1)) = x n}
  zero_mem' := fun n => map_zero (f n)
  add_mem' := by
    intro x y hx hy n
    change f n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro r x hx n
    change f n (PadicInt.toZModPow (n + 1) r • x (n + 1)) =
      PadicInt.toZModPow n r • x n
    rw [step_smul, compatible_residue, hx n]

variable (B : ℕ → Type v) [∀ n, AddCommGroup (B n)] [∀ n, Module (ZMod (l ^ n)) (B n)]
variable (g : ∀ n, B (n + 1) →+ B n)
variable (e : ∀ n, A n ≃+ B n)
variable (h : ∀ n a, e n (f n a) = g n (e (n + 1) a))

/-- An actual levelwise comparison preserving transitions identifies the
native p-adic scalar action on both compatible systems. -/
def linearEquiv :
    ↥(compatible l A f) ≃ₗ[ℤ_[l]] ↥(compatible l B g) where
  toFun x := ⟨fun n => e n (x.val n), fun n => by
    rw [← h]
    exact congrArg (e n) (x.property n)⟩
  invFun y := ⟨fun n => (e n).symm (y.val n), fun n => by
    apply (e n).injective
    rw [h, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact y.property n⟩
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply (x.val n))
  right_inv y := Subtype.ext (funext fun n => (e n).apply_symm_apply (y.val n))
  map_add' x y := Subtype.ext (funext fun n => (e n).map_add (x.val n) (y.val n))
  map_smul' r x := Subtype.ext (funext fun n =>
    ((e n).toAddMonoidHom.toZModLinearMap (l ^ n)).map_smul (PadicInt.toZModPow n r) (x.val n))

end

end ManuscriptAudit.PadicBoundedTorsionTower

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PadicBoundedTorsionTower.linearEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
