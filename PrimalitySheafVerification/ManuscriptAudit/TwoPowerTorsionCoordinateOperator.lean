import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionCompatibleBasis

/-! Native torsion endomorphisms give compatible linear operators in the chosen coordinates. -/

namespace ManuscriptAudit.TwoPowerTorsionCoordinateOperator

open TorsionFrobeniusModule TwoPowerTorsionTower
open TwoPowerTorsionCompatibleBasis TwoPowerTorsionReduction

noncomputable section

abbrev Coordinates (n : ℕ) := ZMod (2 ^ n) × ZMod (2 ^ n)

def reducePair (n : ℕ) (a : Coordinates (n + 1)) : Coordinates n :=
  (reduction n a.1, reduction n a.2)

variable (G : Type*) [AddCommGroup G]
variable (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
variable (hfour : Nat.card (Torsion 2 G) = 4)

def operator (f : G →+ G) (n : ℕ) : Module.End (ZMod (2 ^ n)) (Coordinates n) :=
  let e := compatibleLevelEquiv G h hfour n
  ((e.symm : PowerTorsion G n →ₗ[ZMod (2 ^ n)] Coordinates n).comp
    ((mapLinear (2 ^ n) f).comp (e : Coordinates n →ₗ[ZMod (2 ^ n)] PowerTorsion G n)))

/-- The transported operator is the native endomorphism on the actual torsion points. -/
theorem operator_apply (f : G →+ G) (n : ℕ) (a : Coordinates n) :
    compatibleLevelEquiv G h hfour n (operator G h hfour f n a) =
      mapLinear (2 ^ n) f (compatibleLevelEquiv G h hfour n a) := by
  let e := compatibleLevelEquiv G h hfour n
  change e (e.symm (mapLinear (2 ^ n) f (e a))) = _
  exact e.apply_symm_apply _

/-- Matrices or operators built from the native maps reduce across levels. -/
theorem operator_reduction (f : G →+ G) (n : ℕ) (a : Coordinates (n + 1)) :
    reducePair n (operator G h hfour f (n + 1) a) =
      operator G h hfour f n (reducePair n a) := by
  apply (compatibleLevelEquiv G h hfour n).injective
  calc
    _ = transition G n (compatibleLevelEquiv G h hfour (n + 1)
        (operator G h hfour f (n + 1) a)) :=
      (transition_compatibleLevelEquiv G h hfour n (operator G h hfour f (n + 1) a)).symm
    _ = transition G n (mapLinear (2 ^ (n + 1)) f (compatibleLevelEquiv G h hfour (n + 1) a)) := by
      rw [operator_apply]
    _ = mapLinear (2 ^ n) f (transition G n (compatibleLevelEquiv G h hfour (n + 1) a)) :=
      map_transition f n (compatibleLevelEquiv G h hfour (n + 1) a)
    _ = mapLinear (2 ^ n) f (compatibleLevelEquiv G h hfour n (reducePair n a)) := by
      simpa only [reducePair] using congrArg (mapLinear (2 ^ n) f)
        (transition_compatibleLevelEquiv G h hfour n a)
    _ = _ := (operator_apply G h hfour f n _).symm

/-- The native finite torsion operator is invertible whenever the point map is injective. -/
def automorphism (f : G →+ G) (hf : Function.Injective f) (n : ℕ) :
    Coordinates n ≃ₗ[ZMod (2 ^ n)] Coordinates n := by
  let e := compatibleLevelEquiv G h hfour n
  letI : NeZero (2 ^ n : ℕ) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  have hi : Function.Injective (operator G h hfour f n) := by
    change Function.Injective (fun a => e.symm (mapLinear (2 ^ n) f (e a)))
    exact e.symm.injective.comp ((mapLinear_injective (2 ^ n) f hf).comp e.injective)
  exact LinearEquiv.ofBijective (operator G h hfour f n) hi.bijective_of_finite

theorem automorphism_apply (f : G →+ G) (hf : Function.Injective f) (n : ℕ)
    (a : Coordinates n) : automorphism G h hfour f hf n a = operator G h hfour f n a := rfl

/-- Inverses of the actual finite Frobenius operators are compatible as well. -/
theorem inverse_reduction (f : G →+ G) (hf : Function.Injective f) (n : ℕ)
    (a : Coordinates (n + 1)) :
    reducePair n ((automorphism G h hfour f hf (n + 1)).symm a) =
      (automorphism G h hfour f hf n).symm (reducePair n a) := by
  let hi := automorphism G h hfour f hf (n + 1)
  let lo := automorphism G h hfour f hf n
  change reducePair n (hi.symm a) = lo.symm (reducePair n a)
  apply lo.injective
  rw [lo.apply_symm_apply]
  have hr := operator_reduction G h hfour f n (hi.symm a)
  change reducePair n (hi (hi.symm a)) = lo (reducePair n (hi.symm a)) at hr
  rw [hi.apply_symm_apply] at hr
  exact hr.symm

end
end ManuscriptAudit.TwoPowerTorsionCoordinateOperator

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTorsionCoordinateOperator.operator_apply,
      ``ManuscriptAudit.TwoPowerTorsionCoordinateOperator.operator_reduction,
      ``ManuscriptAudit.TwoPowerTorsionCoordinateOperator.inverse_reduction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
