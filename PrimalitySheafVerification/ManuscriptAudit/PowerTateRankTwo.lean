import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionCompatibleBasis

/-! Compatible torsion bases induce a rank-two basis over the actual prime-adic integers. -/

namespace ManuscriptAudit.PowerTateRankTwo

open TorsionFrobeniusModule PowerTorsionTower PowerTateModule
open PowerTorsionCompatibleBasis

noncomputable section

variable (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G]
variable (B : Module.Basis (Fin 2) (ZMod (p ^ 1)) (PowerTorsion p G 1))
variable (h : Function.Surjective (fun P : G => p • P))

local notation "basisAt" => levelEquiv p G B (Nat.Prime.pos (Fact.out : Nat.Prime p)) h
local notation "residue" => PadicInt.toZModPow (p := p)

def fromPadicPair : (ℤ_[p] × ℤ_[p]) →ₗ[ℤ_[p]] Tate p G where
  toFun a := ⟨fun n => basisAt n (residue n a.1, residue n a.2), fun n => by
    rw [transition_levelEquiv, compatible_residue, compatible_residue]⟩
  map_add' a b := by
    apply PowerTateModule.ext p G
    intro n
    change basisAt n (residue n (a.1 + b.1), residue n (a.2 + b.2)) =
      basisAt n (residue n a.1, residue n a.2) + basisAt n (residue n b.1, residue n b.2)
    rw [map_add (residue n) a.1 b.1, map_add (residue n) a.2 b.2]
    exact (basisAt n).map_add (residue n a.1, residue n a.2) (residue n b.1, residue n b.2)
  map_smul' r a := by
    apply PowerTateModule.ext p G
    intro n
    change basisAt n (residue n (r * a.1), residue n (r * a.2)) =
      residue n r • basisAt n (residue n a.1, residue n a.2)
    rw [map_mul, map_mul, ← map_smul] <;> rfl

@[simp] theorem evaluate_fromPadicPair (n : ℕ) (a : ℤ_[p] × ℤ_[p]) :
    evaluate p G n (fromPadicPair p G B h a) =
      basisAt n (residue n a.1, residue n a.2) := rfl

private theorem fromPadicPair_injective : Function.Injective (fromPadicPair p G B h) := by
  intro a b hab
  have e (n : ℕ) : (residue n a.1, residue n a.2) = (residue n b.1, residue n b.2) :=
    (basisAt n).injective (congrArg (evaluate p G n) hab)
  exact Prod.ext (PadicInt.ext_of_toZModPow.mp fun n => congrArg Prod.fst (e n))
    (PadicInt.ext_of_toZModPow.mp fun n => congrArg Prod.snd (e n))

private def residuesOf (x : Tate p G) (n : ℕ) : ZMod (p ^ n) × ZMod (p ^ n) :=
  (basisAt n).symm (evaluate p G n x)

private theorem residuesOf_compatible (x : Tate p G) (n : ℕ) :
    (PadicResidueSystems.reduction p (Nat.le_succ n) (residuesOf p G B h x (n + 1)).1,
      PadicResidueSystems.reduction p (Nat.le_succ n) (residuesOf p G B h x (n + 1)).2) =
      residuesOf p G B h x n := by
  apply (basisAt n).injective
  rw [← transition_levelEquiv]
  simp only [residuesOf, LinearEquiv.apply_symm_apply, evaluate_transition]

private theorem fromPadicPair_surjective : Function.Surjective (fromPadicPair p G B h) := by
  intro x
  let v := residuesOf p G B h x
  let s : PadicResidueSystems.systems p := ⟨fun n => (v n).1,
    PadicResidueSystems.compatible_of_successors p _ fun n => by
      exact congrArg Prod.fst (residuesOf_compatible p G B h x n)⟩
  let t : PadicResidueSystems.systems p := ⟨fun n => (v n).2,
    PadicResidueSystems.compatible_of_successors p _ fun n => by
      exact congrArg Prod.snd (residuesOf_compatible p G B h x n)⟩
  let e := PadicResidueSystems.padicRingEquiv p
  refine ⟨(e.symm s, e.symm t), PowerTateModule.ext p G fun n => ?_⟩
  have hs : residue n (e.symm s) = (v n).1 :=
    congrArg (PadicResidueSystems.evaluate p n) (e.apply_symm_apply s)
  have ht : residue n (e.symm t) = (v n).2 :=
    congrArg (PadicResidueSystems.evaluate p n) (e.apply_symm_apply t)
  rw [evaluate_fromPadicPair]
  change basisAt n (residue n (e.symm s), residue n (e.symm t)) = evaluate p G n x
  rw [hs, ht]
  exact (basisAt n).apply_symm_apply _

def padicPairEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] Tate p G :=
  LinearEquiv.ofBijective (fromPadicPair p G B h)
    ⟨fromPadicPair_injective p G B h, fromPadicPair_surjective p G B h⟩

theorem evaluate_padicPairEquiv (n : ℕ) (a : ℤ_[p] × ℤ_[p]) :
    evaluate p G n (padicPairEquiv p G B h a) =
      basisAt n (residue n a.1, residue n a.2) := rfl

end
end ManuscriptAudit.PowerTateRankTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateRankTwo.evaluate_fromPadicPair,
      ``ManuscriptAudit.PowerTateRankTwo.padicPairEquiv,
      ``ManuscriptAudit.PowerTateRankTwo.evaluate_padicPairEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
