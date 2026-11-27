import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTateModule

/-! Injective point maps are automorphisms on Tate modules with finite torsion levels. -/

namespace ManuscriptAudit.TwoPowerTateAutomorphism

open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTateModule

noncomputable section

variable {G : Type*} [AddCommGroup G]
variable (f : G →+ G) (hf : Function.Injective f)
variable (hfinite : ∀ n, Finite (PowerTorsion G n))

private def levelEquiv (n : ℕ) :
    PowerTorsion G n ≃ₗ[ZMod (2 ^ n)] PowerTorsion G n := by
  letI := hfinite n
  exact LinearEquiv.ofBijective (mapLinear (2 ^ n) f)
    (mapLinear_injective (2 ^ n) f hf).bijective_of_finite

private theorem inverse_transition (n : ℕ) (a : PowerTorsion G (n + 1)) :
    transition G n ((levelEquiv f hf hfinite (n + 1)).symm a) =
      (levelEquiv f hf hfinite n).symm (transition G n a) := by
  let e := levelEquiv f hf hfinite (n + 1)
  let d := levelEquiv f hf hfinite n
  change transition G n (e.symm a) = d.symm (transition G n a)
  apply d.injective
  rw [d.apply_symm_apply]
  have hn := (map_transition f n (e.symm a)).symm
  change d (transition G n (e.symm a)) = transition G n (e (e.symm a)) at hn
  rwa [e.apply_symm_apply] at hn

def mapEquiv : Tate G ≃ₗ[ℤ_[2]] Tate G :=
  LinearEquiv.ofBijective (TwoPowerTateModule.map f) ⟨map_injective f hf, by
    intro x
    refine ⟨⟨fun n => (levelEquiv f hf hfinite n).symm (evaluate G n x), fun n => ?_⟩, ?_⟩
    · rw [inverse_transition, evaluate_transition]
    · apply TwoPowerTateModule.ext G
      intro n
      exact (levelEquiv f hf hfinite n).apply_symm_apply _⟩

theorem evaluate_mapEquiv (n : ℕ) (x : Tate G) :
    evaluate G n (mapEquiv f hf hfinite x) = mapLinear (2 ^ n) f (evaluate G n x) := rfl

end
end ManuscriptAudit.TwoPowerTateAutomorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTateAutomorphism.mapEquiv,
      ``ManuscriptAudit.TwoPowerTateAutomorphism.evaluate_mapEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
