import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionLift
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionReduction

/-! Simultaneously compatible free coordinates on every native two-power torsion level. -/

namespace ManuscriptAudit.TwoPowerTorsionCompatibleBasis

open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTorsionBasis
open TwoPowerTorsionLift TwoPowerTorsionReduction

noncomputable section

variable (G : Type*) [AddCommGroup G]

private def orderTwoBasis (hfour : Nat.card (Torsion 2 G) = 4) :
    Module.Basis (Fin 2) (ZMod 2) (PowerTorsion G 1) := by
  letI : Finite (Torsion 2 G) := Nat.finite_of_card_ne_zero (by rw [hfour]; decide)
  exact FrobeniusModTwoLinear.basisOfCardFour _ hfour

variable (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
variable (hfour : Nat.card (Torsion 2 G) = 4)

/-- The selected pair of generators at each positive level lifts the same order-two pair. -/
def generator (i : Fin 2) (n : ℕ) : PowerTorsion G (n + 1) :=
  lifted G h (orderTwoBasis G hfour i) n

theorem generator_transition (i : Fin 2) (n : ℕ) :
    transition G (n + 1) (generator G h hfour i (n + 1)) = generator G h hfour i n :=
  transition_lifted G h (orderTwoBasis G hfour i) n

private theorem generator_scale_nonzero (i : Fin 2) (n : ℕ) :
    (2 ^ n : ℕ) • (generator G h hfour i n : G) ≠ 0 := by
  rw [generator, scale_lifted]
  intro hz
  exact (orderTwoBasis G hfour).ne_zero i (Subtype.ext hz)

private theorem generator_scale_ne (n : ℕ) :
    (2 ^ n : ℕ) • (generator G h hfour 0 n : G) ≠
      (2 ^ n : ℕ) • (generator G h hfour 1 n : G) := by
  simp only [generator, scale_lifted]
  intro he
  exact (by decide : (0 : Fin 2) ≠ 1) ((orderTwoBasis G hfour).injective (Subtype.ext he))

/-- Bases chosen simultaneously so that the reduction square commutes. -/
def compatibleLevelEquiv : (n : ℕ) →
    (ZMod (2 ^ n) × ZMod (2 ^ n)) ≃ₗ[ZMod (2 ^ n)] PowerTorsion G n
  | 0 => zeroLevelEquiv G
  | n + 1 =>
    levelEquivFromLifts G h hfour n (generator G h hfour 0 n) (generator G h hfour 1 n)
      (generator_scale_nonzero G h hfour 0 n) (generator_scale_nonzero G h hfour 1 n)
      (generator_scale_ne G h hfour n)

theorem compatibleLevelEquiv_succ_apply (n : ℕ)
    (a : ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1))) :
    compatibleLevelEquiv G h hfour (n + 1) a =
      a.1 • generator G h hfour 0 n + a.2 • generator G h hfour 1 n := by
  rw [compatibleLevelEquiv, levelEquivFromLifts_apply]

/-- Actual doubling is coordinatewise scalar reduction in the compatible bases. -/
theorem transition_compatibleLevelEquiv (n : ℕ)
    (a : ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1))) :
    transition G n (compatibleLevelEquiv G h hfour (n + 1) a) =
      compatibleLevelEquiv G h hfour n (reduction n a.1, reduction n a.2) := by
  cases n with
  | zero =>
    have hz (P : PowerTorsion G 0) : (P : G) = 0 := by
      simpa only [pow_zero, one_nsmul] using (mem_iff (2 ^ 0) G _).mp P.property
    exact Subtype.ext ((hz _).trans (hz _).symm)
  | succ n =>
    simp only [compatibleLevelEquiv_succ_apply, map_add, transition_smul, generator_transition]

def compatibleLevelBasis (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ n)) (PowerTorsion G n) :=
  Module.Basis.ofEquivFun
    ((compatibleLevelEquiv G h hfour n).symm.trans
      ((LinearEquiv.finTwoArrow (ZMod (2 ^ n)) (ZMod (2 ^ n))).symm))

end
end ManuscriptAudit.TwoPowerTorsionCompatibleBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTorsionCompatibleBasis.generator_transition,
      ``ManuscriptAudit.TwoPowerTorsionCompatibleBasis.transition_compatibleLevelEquiv,
      ``ManuscriptAudit.TwoPowerTorsionCompatibleBasis.compatibleLevelBasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
