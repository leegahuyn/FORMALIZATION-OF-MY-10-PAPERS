import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Injective point maps are automorphisms on Tate modules with finite torsion levels. -/

namespace ManuscriptAudit.PowerTateAutomorphism

open TorsionFrobeniusModule PowerTorsionTower PowerTateModule

noncomputable section

variable (l : ℕ) [Fact l.Prime]
variable {G : Type*} [AddCommGroup G]
variable (f : G →+ G) (hf : Function.Injective f)
variable (hfinite : ∀ n, Finite (PowerTorsion l G n))

private def levelEquiv (n : ℕ) :
    PowerTorsion l G n ≃ₗ[ZMod (l ^ n)] PowerTorsion l G n := by
  letI := hfinite n
  exact LinearEquiv.ofBijective (mapLinear (l ^ n) f)
    (mapLinear_injective (l ^ n) f hf).bijective_of_finite

private theorem inverse_transition (n : ℕ) (a : PowerTorsion l G (n + 1)) :
    transition l G n ((levelEquiv l f hf hfinite (n + 1)).symm a) =
      (levelEquiv l f hf hfinite n).symm (transition l G n a) := by
  let e := levelEquiv l f hf hfinite (n + 1)
  let d := levelEquiv l f hf hfinite n
  change transition l G n (e.symm a) = d.symm (transition l G n a)
  apply d.injective
  rw [d.apply_symm_apply]
  have hn := (map_transition l f n (e.symm a)).symm
  change d (transition l G n (e.symm a)) = transition l G n (e (e.symm a)) at hn
  rwa [e.apply_symm_apply] at hn

def mapEquiv : Tate l G ≃ₗ[ℤ_[l]] Tate l G :=
  LinearEquiv.ofBijective (PowerTateModule.map l f) ⟨map_injective l f hf, by
    intro x
    refine ⟨⟨fun n => (levelEquiv l f hf hfinite n).symm (evaluate l G n x), fun n => ?_⟩, ?_⟩
    · rw [inverse_transition, evaluate_transition]
    · apply PowerTateModule.ext l G
      intro n
      exact (levelEquiv l f hf hfinite n).apply_symm_apply _⟩

theorem evaluate_mapEquiv (n : ℕ) (x : Tate l G) :
    evaluate l G n (mapEquiv l f hf hfinite x) = mapLinear (l ^ n) f (evaluate l G n x) := rfl

end
end ManuscriptAudit.PowerTateAutomorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateAutomorphism.mapEquiv,
      ``ManuscriptAudit.PowerTateAutomorphism.evaluate_mapEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
