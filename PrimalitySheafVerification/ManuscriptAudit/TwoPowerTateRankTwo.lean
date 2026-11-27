import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTateModule
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionCompatibleBasis

/-! Compatible torsion bases induce a rank-two basis over the actual 2-adic integers. -/

namespace ManuscriptAudit.TwoPowerTateRankTwo

open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTateModule
open TwoPowerTorsionCompatibleBasis

noncomputable section

variable (G : Type*) [AddCommGroup G]
variable (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
variable (hfour : Nat.card (Torsion 2 G) = 4)

local notation "basisAt" => compatibleLevelEquiv G h hfour
local notation "residue" => PadicInt.toZModPow (p := 2)

def fromPadicPair : (ℤ_[2] × ℤ_[2]) →ₗ[ℤ_[2]] Tate G where
  toFun a := ⟨fun n => basisAt n (residue n a.1, residue n a.2), fun n => by
    rw [transition_compatibleLevelEquiv, compatible_residue, compatible_residue]⟩
  map_add' a b := by
    apply TwoPowerTateModule.ext G
    intro n
    change basisAt n (residue n (a.1 + b.1), residue n (a.2 + b.2)) =
      basisAt n (residue n a.1, residue n a.2) + basisAt n (residue n b.1, residue n b.2)
    rw [map_add (residue n) a.1 b.1, map_add (residue n) a.2 b.2]
    exact (basisAt n).map_add (residue n a.1, residue n a.2) (residue n b.1, residue n b.2)
  map_smul' r a := by
    apply TwoPowerTateModule.ext G
    intro n
    change basisAt n (residue n (r * a.1), residue n (r * a.2)) =
      residue n r • basisAt n (residue n a.1, residue n a.2)
    rw [map_mul, map_mul, ← map_smul] <;> rfl

@[simp] theorem evaluate_fromPadicPair (n : ℕ) (a : ℤ_[2] × ℤ_[2]) :
    evaluate G n (fromPadicPair G h hfour a) =
      basisAt n (residue n a.1, residue n a.2) := rfl

private theorem fromPadicPair_injective : Function.Injective (fromPadicPair G h hfour) := by
  intro a b hab
  have e (n : ℕ) : (residue n a.1, residue n a.2) = (residue n b.1, residue n b.2) :=
    (basisAt n).injective (congrArg (evaluate G n) hab)
  exact Prod.ext (PadicInt.ext_of_toZModPow.mp fun n => congrArg Prod.fst (e n))
    (PadicInt.ext_of_toZModPow.mp fun n => congrArg Prod.snd (e n))

private def residuesOf (x : Tate G) (n : ℕ) : ZMod (2 ^ n) × ZMod (2 ^ n) :=
  (basisAt n).symm (evaluate G n x)

private theorem residuesOf_compatible (x : Tate G) (n : ℕ) :
    (TwoPowerTorsionReduction.reduction n (residuesOf G h hfour x (n + 1)).1,
      TwoPowerTorsionReduction.reduction n (residuesOf G h hfour x (n + 1)).2) =
      residuesOf G h hfour x n := by
  apply (basisAt n).injective
  rw [← transition_compatibleLevelEquiv]
  simp only [residuesOf, LinearEquiv.apply_symm_apply, evaluate_transition]

private theorem fromPadicPair_surjective : Function.Surjective (fromPadicPair G h hfour) := by
  intro x
  let v := residuesOf G h hfour x
  have eq (n : ℕ) : TwoPowerTorsionReduction.reduction n =
      PadicResidueSystems.reduction 2 (Nat.le_succ n) := RingHom.ext_zmod _ _
  let s : PadicResidueSystems.systems 2 := ⟨fun n => (v n).1,
    PadicResidueSystems.compatible_of_successors 2 _ fun n => by
      rw [← eq n]
      exact congrArg Prod.fst (residuesOf_compatible G h hfour x n)⟩
  let t : PadicResidueSystems.systems 2 := ⟨fun n => (v n).2,
    PadicResidueSystems.compatible_of_successors 2 _ fun n => by
      rw [← eq n]
      exact congrArg Prod.snd (residuesOf_compatible G h hfour x n)⟩
  let e := PadicResidueSystems.padicRingEquiv 2
  refine ⟨(e.symm s, e.symm t), TwoPowerTateModule.ext G fun n => ?_⟩
  have hs : residue n (e.symm s) = (v n).1 :=
    congrArg (PadicResidueSystems.evaluate 2 n) (e.apply_symm_apply s)
  have ht : residue n (e.symm t) = (v n).2 :=
    congrArg (PadicResidueSystems.evaluate 2 n) (e.apply_symm_apply t)
  rw [evaluate_fromPadicPair]
  change basisAt n (residue n (e.symm s), residue n (e.symm t)) = evaluate G n x
  rw [hs, ht]
  exact (basisAt n).apply_symm_apply _

def padicPairEquiv : (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] Tate G :=
  LinearEquiv.ofBijective (fromPadicPair G h hfour)
    ⟨fromPadicPair_injective G h hfour, fromPadicPair_surjective G h hfour⟩

theorem evaluate_padicPairEquiv (n : ℕ) (a : ℤ_[2] × ℤ_[2]) :
    evaluate G n (padicPairEquiv G h hfour a) =
      basisAt n (residue n a.1, residue n a.2) := rfl

end
end ManuscriptAudit.TwoPowerTateRankTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTateRankTwo.evaluate_fromPadicPair,
      ``ManuscriptAudit.TwoPowerTateRankTwo.padicPairEquiv,
      ``ManuscriptAudit.TwoPowerTateRankTwo.evaluate_padicPairEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
