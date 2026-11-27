import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateRankTwo

/-! The compatible prime-adic Tate module maps onto every native torsion level. -/

namespace ManuscriptAudit.PowerTateEvaluationSurjective

open PowerTateModule PowerTateRankTwo PowerTorsionTower PowerTorsionCompatibleBasis
open TorsionFrobeniusModule

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (B : Module.Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (h : Function.Surjective (fun P : G => l • P))

include B h

theorem evaluate_surjective (n : ℕ) : Function.Surjective (evaluate l G n) := by
  letI : NeZero (l ^ n : ℕ) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e := levelEquiv l G B (Fact.out : l.Prime).pos h n
  intro P
  let a := e.symm P
  have hResidue (r : ZMod (l ^ n)) : PadicInt.toZModPow n (r.val : ℤ_[l]) = r := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  refine ⟨padicPairEquiv l G B h (a.1.val, a.2.val), ?_⟩
  rw [evaluate_padicPairEquiv, hResidue, hResidue]
  exact e.apply_symm_apply P

/-- A scalar identity on the whole Tate module gives the same reduced scalar on a finite level. -/
theorem scalar_reduction (r : AddMonoid.End G) (c : ℤ_[l])
    (he : endMap l r = c • (1 : Module.End ℤ_[l] (Tate l G))) (n : ℕ) :
    mapLinear (l ^ n) r =
      PadicInt.toZModPow n c • (1 : Module.End (ZMod (l ^ n)) (PowerTorsion l G n)) := by
  apply LinearMap.ext
  intro P
  obtain ⟨x, rfl⟩ := evaluate_surjective l G B h n P
  change mapLinear (l ^ n) r (evaluate l G n x) = PadicInt.toZModPow n c • evaluate l G n x
  rw [← evaluate_endMap, he]
  exact evaluate_smul l G n c x

end
end ManuscriptAudit.PowerTateEvaluationSurjective

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateEvaluationSurjective.evaluate_surjective,
      ``ManuscriptAudit.PowerTateEvaluationSurjective.scalar_reduction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
