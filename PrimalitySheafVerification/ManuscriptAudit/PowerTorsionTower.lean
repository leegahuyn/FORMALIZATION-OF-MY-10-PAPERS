import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! Exact multiplication transitions on the native tower of torsion groups. -/

namespace ManuscriptAudit.PowerTorsionTower

open TorsionFrobeniusModule

noncomputable section

variable (m : ℕ) (G : Type*) [AddCommGroup G]

abbrev PowerTorsion (n : ℕ) := Torsion (m ^ n) G

/-- The native multiplication-by-m map from the (n+1)st torsion group onto the nth. -/
def transition (n : ℕ) : PowerTorsion m G (n + 1) →+ PowerTorsion m G n where
  toFun P := ⟨m • (P : G), (mem_iff (m ^ n) G _).mpr (by
    rw [← mul_nsmul', ← pow_succ]
    exact (mem_iff (m ^ (n + 1)) G _).mp P.property)⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' P Q := Subtype.ext (nsmul_add (P : G) (Q : G) _)

@[simp] theorem transition_inclusion (n : ℕ) (P : PowerTorsion m G (n + 1)) :
    (transition m G n P : G) = m • (P : G) := rfl

theorem transition_surjective
    (h : Function.Surjective (fun P : G => m • P)) (n : ℕ) :
    Function.Surjective (transition m G n) := by
  intro Q
  obtain ⟨P, hP⟩ := h (Q : G)
  change m • P = (Q : G) at hP
  have hT : (m ^ (n + 1) : ℕ) • P = 0 := by
    rw [pow_succ, mul_nsmul', hP]
    exact (mem_iff (m ^ n) G _).mp Q.property
  refine ⟨⟨P, (mem_iff (m ^ (n + 1)) G _).mpr hT⟩, Subtype.ext ?_⟩
  exact hP

/-- Every transition kernel is literally the native subgroup killed by m. -/
def transitionKernelEquiv (n : ℕ) : ↥((transition m G n).ker) ≃ Torsion m G where
  toFun P := ⟨(P.val : G), (mem_iff m G _).mpr (by
    have hp : transition m G n P.val = 0 := AddMonoidHom.mem_ker.mp P.property
    exact congrArg (fun Q : PowerTorsion m G n => (Q : G)) hp)⟩
  invFun Q := by
    have hq : m • (Q : G) = 0 := (mem_iff m G _).mp Q.property
    have hn : (m ^ (n + 1) : ℕ) • (Q : G) = 0 := by
      rw [pow_succ, mul_nsmul', hq, nsmul_zero]
    let P : PowerTorsion m G (n + 1) := ⟨Q, (mem_iff (m ^ (n + 1)) G _).mpr hn⟩
    exact ⟨P, AddMonoidHom.mem_ker.mpr (Subtype.ext hq)⟩
  left_inv P := Subtype.ext (Subtype.ext rfl)
  right_inv Q := Subtype.ext rfl

theorem transition_card_mul
    (h : Function.Surjective (fun P : G => m • P)) (n : ℕ) :
    Nat.card (PowerTorsion m G (n + 1)) =
      Nat.card (PowerTorsion m G n) * Nat.card (Torsion m G) := by
  let f := transition m G n
  calc
    _ = Nat.card (PowerTorsion m G (n + 1) ⧸ f.ker) * Nat.card f.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    _ = _ := congrArg₂ (· * ·)
      (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
        f (transition_surjective m G h n)).toEquiv)
      (Nat.card_congr (transitionKernelEquiv m G n))

/-- The cardinality at every level is the corresponding power of the first level. -/
theorem card_powerTorsion
    (h : Function.Surjective (fun P : G => m • P)) (n : ℕ) :
    Nat.card (PowerTorsion m G n) = Nat.card (Torsion m G) ^ n := by
  induction n with
  | zero =>
    letI : Unique (PowerTorsion m G 0) := ⟨⟨0⟩, fun P => Subtype.ext (by
      change (P : G) = 0
      simpa only [pow_zero, one_nsmul] using (mem_iff (m ^ 0) G _).mp P.property)⟩
    rw [Nat.card_unique, pow_zero]
  | succ n ih => rw [transition_card_mul m G h n, ih, pow_succ]

theorem transition_smul (hm : m ≠ 0) (n : ℕ) (r : ZMod (m ^ (n + 1)))
    (P : PowerTorsion m G (n + 1)) :
    transition m G n (r • P) =
      PadicResidueSystems.reduction m (Nat.le_succ n) r • transition m G n P := by
  letI : NeZero (m ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ hm⟩
  have hs : r • P = r.val • P := by
    calc
      _ = (r.val : ZMod (m ^ (n + 1))) • P :=
        congrArg (fun s : ZMod (m ^ (n + 1)) => s • P) (ZMod.natCast_zmod_val r).symm
      _ = _ := by rw [Nat.cast_smul_eq_nsmul]
  have hr : PadicResidueSystems.reduction m (Nat.le_succ n) r = (r.val : ZMod (m ^ n)) := by
    calc
      _ = PadicResidueSystems.reduction m (Nat.le_succ n) (r.val : ZMod (m ^ (n + 1))) :=
        congrArg (PadicResidueSystems.reduction m (Nat.le_succ n)) (ZMod.natCast_zmod_val r).symm
      _ = _ := map_natCast _ _
  rw [hs, hr, Nat.cast_smul_eq_nsmul, map_nsmul]

variable {G} {H : Type*} [AddCommGroup H]

/-- The transitions commute with every native additive map, including point Frobenius. -/
theorem map_transition (f : G →+ H) (n : ℕ) (P : PowerTorsion m G (n + 1)) :
    transition m H n (mapAdd (m ^ (n + 1)) f P) =
      mapAdd (m ^ n) f (transition m G n P) :=
  Subtype.ext (map_nsmul f m (P : G)).symm

end
end ManuscriptAudit.PowerTorsionTower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTorsionTower.transition_inclusion,
      ``ManuscriptAudit.PowerTorsionTower.transition_surjective,
      ``ManuscriptAudit.PowerTorsionTower.transitionKernelEquiv,
      ``ManuscriptAudit.PowerTorsionTower.transition_card_mul,
      ``ManuscriptAudit.PowerTorsionTower.card_powerTorsion,
      ``ManuscriptAudit.PowerTorsionTower.transition_smul,
      ``ManuscriptAudit.PowerTorsionTower.map_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
