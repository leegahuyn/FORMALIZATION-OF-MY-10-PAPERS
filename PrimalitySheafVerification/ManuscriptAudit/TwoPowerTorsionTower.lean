import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Exact doubling transitions on the native tower of two-power torsion groups. -/

namespace ManuscriptAudit.TwoPowerTorsionTower

open TorsionFrobeniusModule

noncomputable section

variable (G : Type*) [AddCommGroup G]

abbrev PowerTorsion (n : ℕ) := Torsion (2 ^ n) G

/-- The native doubling map from the (n+1)st torsion group onto the nth. -/
def transition (n : ℕ) : PowerTorsion G (n + 1) →+ PowerTorsion G n where
  toFun P := ⟨2 • (P : G), (mem_iff (2 ^ n) G _).mpr (by
    rw [← mul_nsmul', ← pow_succ]
    exact (mem_iff (2 ^ (n + 1)) G _).mp P.property)⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' P Q := Subtype.ext (nsmul_add (P : G) (Q : G) _)

@[simp] theorem transition_inclusion (n : ℕ) (P : PowerTorsion G (n + 1)) :
    (transition G n P : G) = 2 • (P : G) := rfl

theorem transition_surjective
    (h : Function.Surjective (fun P : G => (2 : ℕ) • P)) (n : ℕ) :
    Function.Surjective (transition G n) := by
  intro Q
  obtain ⟨P, hP⟩ := h (Q : G)
  have hT : (2 ^ (n + 1) : ℕ) • P = 0 := by
    rw [pow_succ, mul_nsmul', hP]
    exact (mem_iff (2 ^ n) G _).mp Q.property
  refine ⟨⟨P, (mem_iff (2 ^ (n + 1)) G _).mpr hT⟩, Subtype.ext ?_⟩
  exact hP

/-- Every transition kernel is literally the native subgroup killed by doubling. -/
def transitionKernelEquiv (n : ℕ) : ↥((transition G n).ker) ≃ Torsion 2 G where
  toFun P := ⟨(P.val : G), (mem_iff 2 G _).mpr (by
    have hp : transition G n P.val = 0 := AddMonoidHom.mem_ker.mp P.property
    exact congrArg (fun Q : PowerTorsion G n => (Q : G)) hp)⟩
  invFun Q := by
    have hq : (2 : ℕ) • (Q : G) = 0 := (mem_iff 2 G _).mp Q.property
    have hn : (2 ^ (n + 1) : ℕ) • (Q : G) = 0 := by
      rw [pow_succ, mul_nsmul', hq, nsmul_zero]
    let P : PowerTorsion G (n + 1) := ⟨Q, (mem_iff (2 ^ (n + 1)) G _).mpr hn⟩
    exact ⟨P, AddMonoidHom.mem_ker.mpr (Subtype.ext hq)⟩
  left_inv P := Subtype.ext (Subtype.ext rfl)
  right_inv Q := Subtype.ext rfl

theorem transition_card_mul
    (h : Function.Surjective (fun P : G => (2 : ℕ) • P)) (n : ℕ) :
    Nat.card (PowerTorsion G (n + 1)) =
      Nat.card (PowerTorsion G n) * Nat.card (Torsion 2 G) := by
  let f := transition G n
  calc
    _ = Nat.card (PowerTorsion G (n + 1) ⧸ f.ker) * Nat.card f.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    _ = _ := congrArg₂ (· * ·)
      (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
        f (transition_surjective G h n)).toEquiv)
      (Nat.card_congr (transitionKernelEquiv G n))

/-- A group with surjective doubling and four two-torsion points has exactly 4^n n-level points. -/
theorem card_powerTorsion
    (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (hfour : Nat.card (Torsion 2 G) = 4) (n : ℕ) :
    Nat.card (PowerTorsion G n) = 4 ^ n := by
  induction n with
  | zero =>
    letI : Unique (PowerTorsion G 0) := ⟨⟨0⟩, fun P => Subtype.ext (by
      simpa only [pow_zero, one_nsmul] using (mem_iff (2 ^ 0) G _).mp P.property)⟩
    rw [Nat.card_unique, pow_zero]
  | succ n ih => rw [transition_card_mul G h n, ih, hfour, pow_succ]

variable {G} {H : Type*} [AddCommGroup H]

/-- The transitions commute with every native additive map, including point Frobenius. -/
theorem map_transition (f : G →+ H) (n : ℕ) (P : PowerTorsion G (n + 1)) :
    transition H n (mapAdd (2 ^ (n + 1)) f P) =
      mapAdd (2 ^ n) f (transition G n P) :=
  Subtype.ext (map_nsmul f (P : G) 2).symm

end
end ManuscriptAudit.TwoPowerTorsionTower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTorsionTower.transition_inclusion,
      ``ManuscriptAudit.TwoPowerTorsionTower.transition_surjective,
      ``ManuscriptAudit.TwoPowerTorsionTower.transitionKernelEquiv,
      ``ManuscriptAudit.TwoPowerTorsionTower.transition_card_mul,
      ``ManuscriptAudit.TwoPowerTorsionTower.card_powerTorsion,
      ``ManuscriptAudit.TwoPowerTorsionTower.map_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
